//==- CFLAndersAliasAnalysis.h - Unification-based Alias Analysis -*- C++-*-==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// This is the interface for LLVM's inclusion-based alias analysis
/// implemented with CFL graph reachability.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_CFLANDERSTAINTANALYSIS_H
#define LLVM_ANALYSIS_CFLANDERSTAINTANALYSIS_H

#include "AliasAnalysisSummary.h"
#include "CFLTaintAnalysisUtils.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Optional.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include <forward_list>
#include <memory>

namespace llvm {

class Function;
class MemoryLocation;
class TargetLibraryInfo;

using TaintedSet = DenseSet<cflta::InstantiatedValue>; 

class CFLAndersTaintResult : public AAResultBase<CFLAndersTaintResult> {
  friend AAResultBase<CFLAndersTaintResult>;

  class FunctionInfo; 

public:
  explicit CFLAndersTaintResult(const TargetLibraryInfo &TLI);
  CFLAndersTaintResult(CFLAndersTaintResult &&RHS);
  ~CFLAndersTaintResult();

  /// Handle invalidation events from the new pass manager.
  /// By definition, this result is stateless and so remains valid.
  bool invalidate(Function &, const PreservedAnalyses &,
                  FunctionAnalysisManager::Invalidator &) {
    return false;
  }

  /// Evict the given function from cache
  void evict(const Function *Fn);

  
  /// Get the summary for the given function
  /// Return nullptr if the summary is not found or not available
  const cflta::AliasTaintSummary *getSummary(const Function &);

  AliasResult query(const MemoryLocation &, const MemoryLocation &);
  AliasResult alias(const MemoryLocation &, const MemoryLocation &);

  const Optional<std::vector<const Value *>> allValueAliases(const Value *);  

  const Optional<std::vector<const Value *>> taintedVals(const Function&);
  
  const DenseMap<const Function*, std::vector<const Value *>> taintedValsInReachableFuncs(const Function &Fn); 

private:
  /// Ensures that the given function is available in the cache.
  /// Returns the appropriate entry from the cache.
  const Optional<FunctionInfo> &ensureCached(const Function &);

  /// Inserts the given Function into the cache.
  void scan(const Function &);

  /// Build summary for a given function
  FunctionInfo buildInfoFrom(const Function &);
  const TargetLibraryInfo &TLI;

  /// Cached mapping of Functions to their StratifiedSets.
  /// If a function's sets are currently being built, it is marked
  /// in the cache as an Optional without a value. This way, if we
  /// have any kind of recursion, it is discernable from a function
  /// that simply has empty sets.
  DenseMap<const Function *, Optional<FunctionInfo>> Cache;

  //Save all globals tainted
  TaintedSet TaintedGlobalVars;

  //Save for each function all formal arguments tainted
  DenseMap<const Function *, TaintedSet> TaintedFormalArgs;

  void propagateInterprocedural(FunctionInfo &); 
  
//to propagate taint to other functions where the globals is used  
  std::forward_list<cflta::FunctionHandle<CFLAndersTaintResult>> Handles;
};

/// Analysis pass providing a never-invalidated alias analysis result.
///
/// FIXME: We really should refactor CFL to use the analysis more heavily, and
/// in particular to leverage invalidation to trigger re-computation.
class CFLAndersAA : public AnalysisInfoMixin<CFLAndersAA> {
  friend AnalysisInfoMixin<CFLAndersAA>;

  static AnalysisKey Key;

public:
  using Result = CFLAndersTaintResult;

  CFLAndersTaintResult run(Function &F, FunctionAnalysisManager &AM);
};

/// Legacy wrapper pass to provide the CFLAndersTaintResult object.
class CFLAndersTaintWrapperPass : public ImmutablePass {
  std::unique_ptr<CFLAndersTaintResult> Result;
  
  bool (*taintPredicate) (Value*);
public:
  static char ID;

  CFLAndersTaintWrapperPass(); 
  CFLAndersTaintResult &getResult() { return *Result; }
  const CFLAndersTaintResult &getResult() const { return *Result; }
 
  //bool runOnModule(Module &M);
  void initializePass() override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
};

ModulePass *createCFLAndersTaintWrapperPass();

} // end namespace llvm

#endif 
