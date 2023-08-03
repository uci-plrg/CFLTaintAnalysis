//===- CFLAndersAliasAnalysis.cpp - Unification-based Alias Analysis ------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements a CFL-based, summary-based alias analysis algorithm. It
// differs from CFLSteensAliasAnalysis in its inclusion-based nature while
// CFLSteensAliasAnalysis is unification-based. This pass has worse performance
// than CFLSteensAliasAnalysis (the worst case complexity of
// CFLAndersAliasAnalysis is cubic, while the worst case complexity of
// CFLSteensAliasAnalysis is almost linear), but it is able to yield more
// precise analysis result. The precision of this analysis is roughly the same
// as that of an one level context-sensitive Andersen's algorithm.
//
// The algorithm used here is based on recursive state machine matching scheme
// proposed in "Demand-driven alias analysis for C" by Xin Zheng and Radu
// Rugina. The general idea is to extend the traditional transitive closure
// algorithm to perform CFL matching along the way: instead of recording
// "whether X is reachable from Y", we keep track of "whether X is reachable
// from Y at state Z", where the "state" field indicates where we are in the CFL
// matching process. To understand the matching better, it is advisable to have
// the state machine shown in Figure 3 of the paper available when reading the
// codes: all we do here is to selectively expand the transitive closure by
// discarding edges that are not recognized by the state machine.
//
// There are two differences between our current implementation and the one
// described in the paper:
// - Our algorithm eagerly computes all alias pairs after the CFLGraph is built,
// while in the paper the authors did the computation in a demand-driven
// fashion. We did not implement the demand-driven algorithm due to the
// additional coding complexity and higher memory profile, but if we found it
// necessary we may switch to it eventually.
// - In the paper the authors use a state machine that does not distinguish
// value reads from value writes. For example, if Y is reachable from X at state
// S3, it may be the case that X is written into Y, or it may be the case that
// there's a third value Z that writes into both X and Y. To make that
// distinction (which is crucial in building function summary as well as
// retrieving mod-ref info), we choose to duplicate some of the states in the
// paper's proposed tate machine. The duplication does not change the set the
// machine accepts. Given a pair of reachable values, it only provides more
// detailed information on which value is being written into and which is being
// read from.
//
//===----------------------------------------------------------------------===//

// N.B. AliasAnalysis as a whole is phrased as a FunctionPass at the moment, and
// CFLAndersAA is interprocedural. This is *technically* A Bad Thing, because
// FunctionPasses are only allowed to inspect the Function that they're being
// run on. Realistically, this likely isn't a problem until we allow
// FunctionPasses to run concurrently.

#include "CFLAndersTaintAnalysis.h"
#include "AliasAnalysisSummary.h"
#include "CFLGraph.h"
#include "CFLTaintAnalysisUtils.h"
#include "CFLGraphBuilder.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include <algorithm>
#include <bitset>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <utility>
#include <vector>

//TODO: implement only searching for aliases of a set of memory locations 
using namespace llvm;
using namespace llvm::cflta;

#define DEBUG_TYPE "cfl-anders-taint"

CFLAndersTaintResult::CFLAndersTaintResult(const TargetLibraryInfo &TLI) : TLI(TLI) {}
CFLAndersTaintResult::CFLAndersTaintResult(CFLAndersTaintResult &&RHS)
    : AAResultBase(std::move(RHS)), TLI(RHS.TLI) {}
CFLAndersTaintResult::~CFLAndersTaintResult() = default;

namespace {

enum class MatchState : uint8_t {
  // The following state represents S1 in the paper.
  FlowFromReadOnly = 0,
  // The following two states together represent S2 in the paper.
  // The 'NoReadWrite' suffix indicates that there exists an alias path that
  // does not contain assignment and reverse assignment edges.
  // The 'ReadOnly' suffix indicates that there exists an alias path that
  // contains reverse assignment edges only.
  FlowFromMemAliasNoReadWrite,
  FlowFromMemAliasReadOnly,
  // The following two states together represent S3 in the paper.
  // The 'WriteOnly' suffix indicates that there exists an alias path that
  // contains assignment edges only.
  // The 'ReadWrite' suffix indicates that there exists an alias path that
  // contains both assignment and reverse assignment edges. Note that if X and Y
  // are reachable at 'ReadWrite' state, it does NOT mean X is both read from
  // and written to Y. Instead, it means that a third value Z is written to both
  // X and Y.
  FlowToWriteOnly,
  FlowToReadWrite,
  // The following two states together represent S4 in the paper.
  FlowToMemAliasWriteOnly,
  FlowToMemAliasReadWrite,
};

raw_ostream &operator << ( raw_ostream& strm, MatchState ms )
{
   const std::string names[] = { "FlowFromReadOnly", "FlowFromMemAliasNoReadWrite", "FlowFromMemAliasReadOnly", "FlowToWriteOnly", "FlowToReadWrite", "FlowToMemAliasWriteOnly", "FlowToMemAliasReadWrite" };
   return strm << names[(int)ms];
}

using StateSet = std::bitset<7>;

const unsigned ReadOnlyStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowFromReadOnly)) |
    (1U << static_cast<uint8_t>(MatchState::FlowFromMemAliasReadOnly));
const unsigned WriteOnlyStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowToWriteOnly)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasWriteOnly));
const unsigned ReadWriteStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowToReadWrite)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasReadWrite));

static bool hasReadOnlyState(StateSet Set) {
  return (Set & StateSet(ReadOnlyStateMask)).any();
}

static bool hasWriteOnlyState(StateSet Set) {
  return (Set & StateSet(WriteOnlyStateMask)).any();
}

static bool hasReadWriteState(StateSet Set) {
  return (Set & StateSet(ReadWriteStateMask)).any();
}

static bool hasReadOrWriteState(StateSet Set) {
  return (Set & (StateSet(ReadWriteStateMask) | StateSet(WriteOnlyStateMask) | StateSet(ReadOnlyStateMask))).any();
}

static bool notMemAliasState(MatchState State) {
     return State == MatchState::FlowFromReadOnly ||
            State == MatchState::FlowToWriteOnly  ||
            State == MatchState::FlowToReadWrite; 
}
// A pair that consists of a value and an offset
struct OffsetValue {
  const Value *Val;
  int64_t Offset;
};

bool operator==(OffsetValue LHS, OffsetValue RHS) {
  return LHS.Val == RHS.Val && LHS.Offset == RHS.Offset;
}

bool operator<(OffsetValue LHS, OffsetValue RHS) {
  return std::less<const Value *>()(LHS.Val, RHS.Val) ||
         (LHS.Val == RHS.Val && LHS.Offset < RHS.Offset);
}

inline raw_ostream &operator<<(raw_ostream &OS, const OffsetValue &OV) {
    return OS << *OV.Val << " at offset " << OV.Offset;
}
// A pair that consists of an InstantiatedValue and an offset
struct OffsetInstantiatedValue {
  InstantiatedValue IVal;
  int64_t Offset;
};

bool operator==(OffsetInstantiatedValue LHS, OffsetInstantiatedValue RHS) {
  return LHS.IVal == RHS.IVal && LHS.Offset == RHS.Offset;
}

inline raw_ostream &operator<<(raw_ostream &OS, const OffsetInstantiatedValue &OIV) {
    return OS << OIV.IVal << " offset " << OIV.Offset;
}

// We use ReachabilitySet to keep track of value aliases (The nonterminal "V" in
// the paper) during the analysis.
using ValueStateMap = DenseMap<InstantiatedValue, StateSet>;

class ValueReachMap : public DenseMap<InstantiatedValue, ValueStateMap> {
public:
  iterator_range<ValueStateMap::const_iterator>
  reachableValueAliases(InstantiatedValue V) const {
    auto Itr = find(V);
    if (Itr == end()) {
      return make_range<ValueStateMap::const_iterator>(ValueStateMap::const_iterator(),
                                                       ValueStateMap::const_iterator());
	}
    return make_range<ValueStateMap::const_iterator>(Itr->second.begin(),
                                                 Itr->second.end());
  }

};

class ReachabilitySet {

  ValueReachMap ReachMap;

public:
  using const_valuestate_iterator = ValueStateMap::const_iterator;
  using const_value_iterator = ValueReachMap::const_iterator;

  // Insert edge 'From->To' at state 'State'
  bool insert(InstantiatedValue From, InstantiatedValue To, MatchState State) {
    assert(From != To);
    auto &States = ReachMap[To][From];
    auto Idx = static_cast<size_t>(State);
    if (!States.test(Idx)) {
      States.set(Idx);
      return true;
    }
    return false;
  }

  // Return the set of all ('From', 'State') pair for a given node 'To'
  iterator_range<const_valuestate_iterator>
  reachableValueAliases(InstantiatedValue V) const {
    return ReachMap.reachableValueAliases(V);
  }

  iterator_range<const_value_iterator> value_mappings() const {
    return make_range<const_value_iterator>(ReachMap.begin(), ReachMap.end());
  }

  const ValueReachMap getRevReachMap() const {
	ValueReachMap RevReachMap;
	for(auto const& outer: ReachMap) {
		for(auto const& inner: outer.second) {
			RevReachMap[inner.first][outer.first] = inner.second;
		}
	}
	return RevReachMap;
  }
};

// We use AliasMemSet to keep track of all memory aliases (the nonterminal "M"
// in the paper) during the analysis.
class AliasMemSet {
  using MemSet = DenseSet<InstantiatedValue>;
  using MemMapType = DenseMap<InstantiatedValue, MemSet>;

  MemMapType MemMap;

public:
  using const_mem_iterator = MemSet::const_iterator;

  bool insert(InstantiatedValue LHS, InstantiatedValue RHS) {
    // Top-level values can never be memory aliases because one cannot take the
    // addresses of them
    assert(LHS.DerefLevel > 0 && RHS.DerefLevel > 0);
    return MemMap[LHS].insert(RHS).second;
  }

  const MemSet *getMemoryAliases(InstantiatedValue V) const {
    auto Itr = MemMap.find(V);
    if (Itr == MemMap.end())
      return nullptr;
    return &Itr->second;
  }
};

// We use AliasAttrMap to keep track of the AliasAttr of each node.
class AliasAttrMap {
  using MapType = DenseMap<InstantiatedValue, AliasAttrs>;

  MapType AttrMap;

public:
  using const_iterator = MapType::const_iterator;

  bool add(InstantiatedValue V, AliasAttrs Attr) {
    auto &OldAttr = AttrMap[V];
    auto NewAttr = OldAttr | Attr;
    if (OldAttr == NewAttr)
      return false;
    OldAttr = NewAttr;
    return true;
  }

  AliasAttrs getAttrs(InstantiatedValue V) const {
    AliasAttrs Attr;
    auto Itr = AttrMap.find(V);
    if (Itr != AttrMap.end())
      Attr = Itr->second;
    return Attr;
  }

  iterator_range<const_iterator> mappings() const {
    return make_range<const_iterator>(AttrMap.begin(), AttrMap.end());
  }
};

struct WorkListItem {
  InstantiatedValue From;
  InstantiatedValue To;
  MatchState State;
};

struct Record {
    InterfaceValue IValue;
    unsigned DerefLevel;
};

struct ValueSummary {
  SmallVector<Record, 4> FromRecords, ToRecords;
};


} // end anonymous namespace

namespace llvm {

// Specialize DenseMapInfo for OffsetValue.
template <> struct DenseMapInfo<OffsetValue> {
  static OffsetValue getEmptyKey() {
    return OffsetValue{DenseMapInfo<const Value *>::getEmptyKey(),
                       DenseMapInfo<int64_t>::getEmptyKey()};
  }

  static OffsetValue getTombstoneKey() {
    return OffsetValue{DenseMapInfo<const Value *>::getTombstoneKey(),
                       DenseMapInfo<int64_t>::getEmptyKey()};
  }

  static unsigned getHashValue(const OffsetValue &OVal) {
    return DenseMapInfo<std::pair<const Value *, int64_t>>::getHashValue(
        std::make_pair(OVal.Val, OVal.Offset));
  }

  static bool isEqual(const OffsetValue &LHS, const OffsetValue &RHS) {
    return LHS == RHS;
  }
};

// Specialize DenseMapInfo for OffsetInstantiatedValue.
template <> struct DenseMapInfo<OffsetInstantiatedValue> {
  static OffsetInstantiatedValue getEmptyKey() {
    return OffsetInstantiatedValue{
        DenseMapInfo<InstantiatedValue>::getEmptyKey(),
        DenseMapInfo<int64_t>::getEmptyKey()};
  }

  static OffsetInstantiatedValue getTombstoneKey() {
    return OffsetInstantiatedValue{
        DenseMapInfo<InstantiatedValue>::getTombstoneKey(),
        DenseMapInfo<int64_t>::getEmptyKey()};
  }

  static unsigned getHashValue(const OffsetInstantiatedValue &OVal) {
    return DenseMapInfo<std::pair<InstantiatedValue, int64_t>>::getHashValue(
        std::make_pair(OVal.IVal, OVal.Offset));
  }

  static bool isEqual(const OffsetInstantiatedValue &LHS,
                      const OffsetInstantiatedValue &RHS) {
    return LHS == RHS;
  }
};


} // end namespace llvm


class CFLAndersTaintResult::FunctionInfo {
  // The set of tainted values
  TaintedSet TaintedVals;

  /// Map a value to other values that may alias it
  /// Since the alias relation is symmetric, to save some space we assume values
  /// are properly ordered: if a and b alias each other, and a < b, then b is in
  /// AliasMap[a] but not vice versa.
  DenseMap<const Value *, std::vector<OffsetValue>> AliasMap;

  //TODO: replace all uses of AliasMap with RevReachMap, which subsumes it.
  // Map a value to its reachable values (i.e. its aliases) and the CFL state it 
  // reaches them in 
  ValueReachMap RevReachMap;

  /// Map a value to its corresponding AliasAttrs
  DenseMap<const Value *, AliasAttrs> AttrMap;

  /// Summary of externally visible effects.
  AliasSummary Summary;

  Optional<AliasAttrs> getAttrs(const Value *) const;

public:
  FunctionInfo(const Function &, const SmallVector<Value *, 4> &,
			   const SmallVector<Value *, 4> &, const ValueReachMap &, 
               const AliasAttrMap &, const TaintedSet &);
  TaintedSet propagateExternalTaint(const TaintedSet&); 
  bool mayAlias(const Value *, LocationSize, const Value *, LocationSize) const;

  Optional<std::vector<const Value *>> getValueAliases(const Value *) const;

  const TaintedSet &getTaintedVals() const { return TaintedVals; }
  const DenseMap<const Value *, AliasAttrs> &getAttrMap() const { return AttrMap; }
  const AliasSummary &getSummary() const { return Summary; }
  const ValueReachMap &getRevReachMap() const { return RevReachMap; }
 
};

static Optional<InterfaceValue>
getInterfaceValue(InstantiatedValue IValue,
				  const Function &Fn,
                  const SmallVectorImpl<Value *> &RetVals,
				  const SmallVectorImpl <Value *> &VAArgs) {
  //Globals are handled in getGlobalInterfaceValue
  auto Val = IValue.Val;

  Optional<unsigned> Index;
  auto ArgSize = Fn.arg_size();
  if (auto Arg = dyn_cast<Argument>(Val))
    Index = Arg->getArgNo() + 1;
  else if (is_contained(VAArgs, Val))
	Index = ArgSize + 1;
  else if (is_contained(RetVals, Val))
    Index = 0;

  if (Index)
    return InterfaceValue{*Index, IValue.DerefLevel};
  return None;
}

static void populateAttrMap(DenseMap<const Value *, AliasAttrs> &AttrMap,
                            const AliasAttrMap &AMap) {
  for (const auto &Mapping : AMap.mappings()) {
    auto IVal = Mapping.first;

    // Insert IVal into the map
    auto &Attr = AttrMap[IVal.Val];
    // AttrMap only cares about top-level values
    if (IVal.DerefLevel == 0)
      Attr |= Mapping.second;
  }
}

static void
populateAliasMap(DenseMap<const Value *, std::vector<OffsetValue>> &AliasMap,
                 const ValueReachMap &RevReachMap) {
  for (const auto &OuterMapping : RevReachMap) {
    // AliasMap only cares about top-level values
    if (OuterMapping.first.DerefLevel > 0)
      continue;

    auto Val = OuterMapping.first.Val;
    auto &AliasList = AliasMap[Val];
    for (const auto &InnerMapping : OuterMapping.second) {
      // Again, AliasMap only cares about top-level values
      if (InnerMapping.first.DerefLevel == 0)
        AliasList.push_back(OffsetValue{InnerMapping.first.Val, UnknownOffset});
    }

    // Sort AliasList for faster lookup
    llvm::sort(AliasList);
  }
}

static DenseMap<Value *, unsigned>buildDepthMap(const ValueReachMap &RevReachMap, const AliasAttrMap &AMap) {
	DenseMap<Value *, unsigned> DepthMap;
	for (auto &Mapping: RevReachMap) {
		auto IVal = Mapping.first;
		auto Itr = DepthMap.find(IVal.Val);
		if(Itr == DepthMap.end() || Itr->second < IVal.DerefLevel)
			 DepthMap[IVal.Val] = IVal.DerefLevel;
	}	
	for (auto &Mapping: AMap.mappings()) {
		auto IVal = Mapping.first;
		auto Itr = DepthMap.find(IVal.Val);
		if(Itr == DepthMap.end() || Itr->second < IVal.DerefLevel)
			 DepthMap[IVal.Val] = IVal.DerefLevel;
	}			
	return DepthMap;
}

static void populateAliasSummary(
	AliasSummary &Summary, const Function &Fn,
    const SmallVectorImpl<Value *> &RetVals, const SmallVectorImpl<Value *> &VAArgs, 
    const ValueReachMap &RevReachMap, const AliasAttrMap &AMap) {

	auto &ExtRelations = Summary.RetParamRelations;
	auto &ExtAttributes = Summary.RetParamAttributes;

  // If a function only returns one of its argument X, then X will be both an
  // argument and a return value at the same time. This is an edge case that
  // needs special handling here.
  for (const auto &Arg : Fn.args()) {
    if (is_contained(RetVals, &Arg)) {
      auto ArgVal = InterfaceValue{Arg.getArgNo() + 1, 0};
      auto RetVal = InterfaceValue{0, 0};
      ExtRelations.push_back(ExternalRelation{ArgVal, RetVal, 0});
    }
  }

 //the case where the function returns a variadic argument
  for (const auto *Arg: VAArgs) {
 	if (is_contained(RetVals, Arg)) {
       auto ArgVal = InterfaceValue{(unsigned)(Fn.arg_size() + 1), 0};
       auto RetVal = InterfaceValue{0, 0};
       ExtRelations.push_back(ExternalRelation{ArgVal, RetVal, 0});
   }
  }
   
  auto DepthMap = buildDepthMap(RevReachMap, AMap);

  for (const auto &OuterMapping : RevReachMap) {
	auto IVal = OuterMapping.first;
    if (auto Src = getInterfaceValue(IVal, Fn, RetVals, VAArgs)) {
	  auto SrcVal = IVal.Val;
	  unsigned MaxLevel = maxDerefLevel(SrcVal);

      DenseSet<std::pair<InstantiatedValue, unsigned>> WorkSet1, WorkSet2;
	  auto *CurWorkSet = &WorkSet1, *NextWorkSet = &WorkSet2;
      CurWorkSet->insert(std::make_pair(IVal, Src->DerefLevel));
      while(!CurWorkSet->empty()) {
        //errs() << "Src: " << *Src << "\n";
   	    for(const auto &Pair : *CurWorkSet) {
		  Src->DerefLevel = Pair.second;
		  auto ExtendedAlias = Pair.first;

   	      auto Attr = getExternallyVisibleAttrs(AMap.getAttrs(ExtendedAlias));
   	      if (Attr.any())
   	        ExtAttributes.push_back(ExternalAttribute{*Src, Attr});
   	   
          for (const auto &InnerMapping : RevReachMap.reachableValueAliases(ExtendedAlias)) {
   	        auto States = InnerMapping.second;
   	        auto Alias = InnerMapping.first;
            // If Src is a param/return value, we get a same-level assignment.
            if (auto Dst = getInterfaceValue(Alias, Fn, RetVals, VAArgs)) {
               
              // This may happen if both Dst and Src are return values
              if (*Dst == *Src)
                continue;
              if (hasReadOnlyState(States))
                ExtRelations.push_back(ExternalRelation{*Dst, *Src, UnknownOffset});
		  	  if (hasWriteOnlyState(States) || hasReadWriteState(States))
                ExtRelations.push_back(ExternalRelation{*Src, *Dst, UnknownOffset});			
            } 
			else if (hasReadOrWriteState(States)) {
			  unsigned NewSrcLevel = DepthMap[SrcVal] + 1;
			  unsigned NewAliasLevel = NewSrcLevel - Src->DerefLevel + Alias.DerefLevel;

			  while(NewAliasLevel <= DepthMap[Alias.Val] &&
					NewSrcLevel <= MaxLevel) {
		        NextWorkSet->insert(std::make_pair(
					InstantiatedValue{Alias.Val, NewAliasLevel},
					NewSrcLevel
				));
				NewSrcLevel ++;
				NewAliasLevel ++;
			  } 
		    }
		  }
        }          
        
		std::swap(CurWorkSet,NextWorkSet);
		NextWorkSet->clear(); 
	    Src->DerefLevel++;
	  }
    } 
  }
}

static void populateExternalRelations(
    SmallVectorImpl<ExternalRelation> &ExtRelations, const Function &Fn,
    const SmallVectorImpl<Value *> &RetVals, const SmallVectorImpl<Value *> &VAArgs, 
	const ValueReachMap &RevReachMap) {
  // If a function only returns one of its argument X, then X will be both an
  // argument and a return value at the same time. This is an edge case that
  // needs special handling here.
  for (const auto &Arg : Fn.args()) {
    if (is_contained(RetVals, &Arg)) {
      auto ArgVal = InterfaceValue{Arg.getArgNo() + 1, 0};
      auto RetVal = InterfaceValue{0, 0};
      ExtRelations.push_back(ExternalRelation{ArgVal, RetVal, 0});
    }
  }

 //the case where the function returns a variadic argument
 for (const auto *Arg: VAArgs) {
	if (is_contained(RetVals, Arg)) {
      auto ArgVal = InterfaceValue{(unsigned)(Fn.arg_size() + 1), 0};
      auto RetVal = InterfaceValue{0, 0};
      ExtRelations.push_back(ExternalRelation{ArgVal, RetVal, 0});
  }
 }

  // Below is the core summary construction logic.
  // A naive solution of adding only the value aliases that are parameters or
  // return values in ReachSet to the summary won't work: It is possible that a
  // parameter P is written into an intermediate value I, and the function
  // subsequently returns *I. In that case, *I is does not value alias anything
  // in ReachSet, and the naive solution will miss a summary edge from (P, 1) to
  // (I, 1).
  // To account for the aforementioned case, we need to check each non-parameter
  // and non-return value for the possibility of acting as an intermediate.
  // 'ValueMap' here records, for each value, which InterfaceValues read from or
  // write into it. If both the read list and the write list of a given value
  // are non-empty, we know that a particular value is an intermidate and we
  // need to add summary edges from the writes to the reads.


  //DenseMap<Value *, ValueSummary> ValueMap;
  for (const auto &OuterMapping : RevReachMap) {
    if (auto Src = getInterfaceValue(OuterMapping.first, Fn, RetVals, VAArgs)) {
      for (const auto &InnerMapping : OuterMapping.second) {
        // If Src is a param/return value, we get a same-level assignment.
        if (auto Dst = getInterfaceValue(InnerMapping.first, Fn, RetVals, VAArgs)) {
          
          // This may happen if both Dst and Src are return values
          if (*Dst == *Src)
            continue;

          if (hasReadOnlyState(InnerMapping.second))
            ExtRelations.push_back(ExternalRelation{*Dst, *Src, UnknownOffset});
          if (hasWriteOnlyState(InnerMapping.second) || hasReadWriteState(InnerMapping.second))
            ExtRelations.push_back(ExternalRelation{*Src, *Dst, UnknownOffset});				
        } else {
		  //growing dereflevels of nodes downwards during propagation replaces this part

          // If Src is not a param/return, add it to ValueMap
          //auto SrcIVal = InnerMapping.first;
		  //if (hasReadOnlyState(InnerMapping.second))
          //  ValueMap[SrcIVal.Val].FromRecords.push_back(
          //      Record{*Dst, SrcIVal.DerefLevel});
          //if (hasWriteOnlyState(InnerMapping.second))
          //  ValueMap[SrcIVal.Val].ToRecords.push_back(
          //      Record{*Dst, SrcIVal.DerefLevel});
        }
      }
    }
  }

 // for (const auto &Mapping : ValueMap) {
 //   for (const auto &FromRecord : Mapping.second.FromRecords) {
 //     for (const auto &ToRecord : Mapping.second.ToRecords) {
 //       auto ToLevel = ToRecord.DerefLevel;
 //       auto FromLevel = FromRecord.DerefLevel;
 //       // Same-level assignments should have already been processed by now
 //       if (ToLevel == FromLevel)
 //         continue;

 //       auto SrcIndex = FromRecord.IValue.Index;
 //       auto SrcLevel = FromRecord.IValue.DerefLevel;
 //       auto DstIndex = ToRecord.IValue.Index;
 //       auto DstLevel = ToRecord.IValue.DerefLevel;
 //       if (ToLevel > FromLevel)
 //         SrcLevel += ToLevel - FromLevel;
 //       else
 //         DstLevel += FromLevel - ToLevel;

 //       ExtRelations.push_back(ExternalRelation{
 //           InterfaceValue{SrcIndex, SrcLevel},
 //           InterfaceValue{DstIndex, DstLevel}, UnknownOffset});
 //     }
 //   }
 // }

  // Remove duplicates in ExtRelations
  llvm::sort(ExtRelations);
  ExtRelations.erase(std::unique(ExtRelations.begin(), ExtRelations.end()),
                     ExtRelations.end());
  //for(auto &extRel : ExtRelations)
	//errs() << "External relation from " << extRel.From << " to " << extRel.To << "\n";
}

static void populateExternalAttributes(
    SmallVectorImpl<ExternalAttribute> &ExtAttributes, const Function &Fn,
    const SmallVectorImpl<Value *> &RetVals, const SmallVectorImpl<Value *> &VAArgs, 
    const AliasAttrMap &AMap) {
  for (const auto &Mapping : AMap.mappings()) {
    if (auto IVal = getInterfaceValue(Mapping.first, Fn, RetVals, VAArgs)) {
      auto Attr = getExternallyVisibleAttrs(Mapping.second);
      if (Attr.any())
        ExtAttributes.push_back(ExternalAttribute{*IVal, Attr});
    }	
  }
}

TaintedSet CFLAndersTaintResult::FunctionInfo::propagateExternalTaint(const TaintedSet &TaintSources) {
	TaintedSet NewTaint;
	for(auto &Source: TaintSources) {
		if(TaintedVals.insert(Source).second) {
			NewTaint.insert(Source);
			//errs() << "external taint source " << Source << "\n";
		}

		for(auto &Mapping: RevReachMap.reachableValueAliases(Source)) {
			if(TaintedVals.insert(Mapping.first).second) {			
				NewTaint.insert(Mapping.first);
				//errs() << "nonread alias of taint source " << Mapping.first << "\n";
			}
		}
	}
	return NewTaint;
}

CFLAndersTaintResult::FunctionInfo::FunctionInfo(
    const Function &Fn, const SmallVector<Value *, 4> &RetVals, 
    const SmallVector<Value *, 4> &VAArgs, const ValueReachMap &RevReachMap, 
    const AliasAttrMap &AMap, const TaintedSet &TaintedVals): TaintedVals(TaintedVals), RevReachMap(RevReachMap) {
  populateAttrMap(AttrMap, AMap);
  //populateExternalAttributes(Summary.RetParamAttributes, Fn, RetVals, VAArgs, AMap);
  populateAliasMap(AliasMap, RevReachMap);
  //populateExternalRelations(Summary.RetParamRelations, Fn, RetVals, VAArgs, RevReachMap);
  populateAliasSummary(Summary, Fn, RetVals, VAArgs, RevReachMap, AMap);
}

void CFLAndersTaintResult::propagateInterprocedural(FunctionInfo &FuncInfo) {
	TaintedSet NewTaint = FuncInfo.getTaintedVals();
	DenseMap<const Function *, TaintedSet> WorkMap;

	while(!NewTaint.empty()) {
		// TODO: If the call is indirect, we might be need to enumerate all
		// potential callees

		for (const auto &Tainted : NewTaint) {					
			for(const auto &Use : Tainted.Val->uses()) {
				if(const auto Call = dyn_cast<CallInst>(Use.getUser())) {
					//arguments are the operands at the beginning in a CallInst
					if(!Call->isArgOperand(&Use))
						continue;
					auto Callee = Call->getCalledFunction();
					if(!Callee)
						continue;
					unsigned ArgNum = CallSite(Call).getArgumentNo(&Use);
					//handle vararg by instantiating to the last argument
					if(Callee->isVarArg() && ArgNum >= Callee->arg_size())
						ArgNum = Callee->arg_size() - 1;
					auto InstantiatedArg = InstantiatedValue{Callee->arg_begin() + ArgNum, Tainted.DerefLevel};
					if(TaintedFormalArgs[Callee].insert(InstantiatedArg).second) {
						if(WorkMap[Callee].insert(InstantiatedArg).second){}
							//errs() << "propagate formal argument taint " << InstantiatedArg << " to function " << Callee->getName() << "\n";
					}
				}

			}

			if(isa<GlobalVariable>(Tainted.Val) 
				&& TaintedGlobalVars.insert(Tainted).second) {
				for(const auto &Use : Tainted.Val->uses()) {
					if(auto Inst = dyn_cast<Instruction>(Use.getUser())) {
						auto Callee = Inst->getFunction();
						if (Callee && WorkMap[Callee].insert(Tainted).second) {}
							//errs() << "propagate global taint to " << Tainted << " in function " << Callee->getName() << "\n";
					}
				}
			}
			
		}	

		NewTaint.clear();
		for (const auto &Pair: WorkMap) {
			auto Itr = Cache.find(Pair.first); 
			if(Itr != Cache.end()) {
				auto &ToPropagate = Itr->second? *Itr->second : FuncInfo;
				NewTaint = ToPropagate.propagateExternalTaint(Pair.second);
			}
		}
		WorkMap.clear();
	}
}

Optional<AliasAttrs>
CFLAndersTaintResult::FunctionInfo::getAttrs(const Value *V) const {
  assert(V != nullptr);

  auto Itr = AttrMap.find(V);
  if (Itr != AttrMap.end())
    return Itr->second;
  return None;
}

bool CFLAndersTaintResult::FunctionInfo::mayAlias(
    const Value *LHS, LocationSize MaybeLHSSize, const Value *RHS,
    LocationSize MaybeRHSSize) const {
  assert(LHS && RHS);

  // Check if we've seen LHS and RHS before. Sometimes LHS or RHS can be created
  // after the analysis gets executed, and we want to be conservative in those
  // cases.
  auto MaybeAttrsA = getAttrs(LHS);
  auto MaybeAttrsB = getAttrs(RHS);
  if (!MaybeAttrsA || !MaybeAttrsB)
    return true;

  // Check AliasAttrs before AliasMap lookup since it's cheaper
  auto AttrsA = *MaybeAttrsA;
  auto AttrsB = *MaybeAttrsB;
  if (hasUnknownOrCallerAttr(AttrsA))
    return AttrsB.any();
  if (hasUnknownOrCallerAttr(AttrsB))
    return AttrsA.any();
  if (isGlobalOrArgAttr(AttrsA))
    return isGlobalOrArgAttr(AttrsB);
  if (isGlobalOrArgAttr(AttrsB))
    return isGlobalOrArgAttr(AttrsA);

  // At this point both LHS and RHS should point to locally allocated objects

  auto Itr = AliasMap.find(LHS);
  if (Itr != AliasMap.end()) {

    // Find out all (X, Offset) where X == RHS
    auto Comparator = [](OffsetValue LHS, OffsetValue RHS) {
      return std::less<const Value *>()(LHS.Val, RHS.Val);
    };
#ifdef EXPENSIVE_CHECKS
    assert(std::is_sorted(Itr->second.begin(), Itr->second.end(), Comparator));
#endif
    auto RangePair = std::equal_range(Itr->second.begin(), Itr->second.end(),
                                      OffsetValue{RHS, 0}, Comparator);

    if (RangePair.first != RangePair.second) {
      // Be conservative about unknown sizes
      if (MaybeLHSSize == LocationSize::unknown() ||
          MaybeRHSSize == LocationSize::unknown())
        return true;

      const uint64_t LHSSize = MaybeLHSSize.getValue();
      const uint64_t RHSSize = MaybeRHSSize.getValue();

      for (const auto &OVal : make_range(RangePair)) {
        // Be conservative about UnknownOffset
        if (OVal.Offset == UnknownOffset)
          return true;

        // We know that LHS aliases (RHS + OVal.Offset) if the control flow
        // reaches here. The may-alias query essentially becomes integer
        // range-overlap queries over two ranges [OVal.Offset, OVal.Offset +
        // LHSSize) and [0, RHSSize).

        // Try to be conservative on super large offsets
        if (LLVM_UNLIKELY(LHSSize > INT64_MAX || RHSSize > INT64_MAX))
          return true;

        auto LHSStart = OVal.Offset;
        // FIXME: Do we need to guard against integer overflow?
        auto LHSEnd = OVal.Offset + static_cast<int64_t>(LHSSize);
        auto RHSStart = 0;
        auto RHSEnd = static_cast<int64_t>(RHSSize);
        if (LHSEnd > RHSStart && LHSStart < RHSEnd)
          return true;
      }
    }
  }

  return false;
}

Optional<std::vector<const Value *>> CFLAndersTaintResult::FunctionInfo::getValueAliases(const Value *V) const {
  auto Itr = AliasMap.find(V);
  if (Itr != AliasMap.end()){
    std::vector<const Value *> vals;
    std::vector<OffsetValue> oVals = Itr->second;
    for (OffsetValue oval: oVals){  
        vals.push_back(oval.Val); //the current analysis is field insensitive
    }
    return vals;
  }
  else 
      return None;
}

static void propagate(InstantiatedValue From, InstantiatedValue To,
                      MatchState State, ReachabilitySet &ReachSet,
                      std::vector<WorkListItem> &WorkList) {
  if (From == To)
    return;
  if (ReachSet.insert(From, To, State)) {

    WorkList.push_back(WorkListItem{From, To, State});
  }

}

static inline bool isPossiblyTainted(const Value *Val, const AliasAttrs Attr) {
	return hasTaintedAttr(Attr) || 
		   (!isValueImmutable(Val) && (hasEscapedAttr(Attr) || hasUnknownAttr(Attr))); 
}

static void initializeWorkList(std::vector<WorkListItem> &WorkList,
                               ReachabilitySet &ReachSet,
                               const CFLGraph &Graph,
                               const SmallVectorImpl<Value *> &RetVals) {
  for (const auto &Mapping : Graph.value_mappings()) {
    auto Val = Mapping.first;
    auto &ValueInfo = Mapping.second;
    assert(ValueInfo.getNumLevels() > 0);
   
	//values with possible external effects 
    if (isa<Argument>(Val) || is_contained(RetVals, Val) || isa<GlobalVariable>(Val)) {
         for (unsigned I = 0, E = ValueInfo.getNumLevels(); I < E; ++I) {
            auto Src = InstantiatedValue{Val, I};
            //might only need to propagate through one direction
			auto NodeInfo = ValueInfo.getNodeInfoAtLevel(I);
            for (auto &Edge : NodeInfo.Edges) {
                propagate(Src, Edge.Other, MatchState::FlowToWriteOnly, ReachSet,
                          WorkList);
            }
            for (auto &Edge : NodeInfo.ReverseEdges) {
                propagate(Src, Edge.Other, MatchState::FlowFromReadOnly, ReachSet,
                          WorkList);
            }

        }
    }
    else { //value is a taint source at some level 
        bool taintedBelow = false;
        for (unsigned I = 0, E = ValueInfo.getNumLevels(); I < E; --E) {
            unsigned Cur = E -1;
            auto Src = InstantiatedValue{Val, Cur};

			auto NodeInfo = ValueInfo.getNodeInfoAtLevel(Cur);
			//nodes above taint sources propagate through both kinds of edges
            if (taintedBelow) { 
                for (auto &Edge : NodeInfo.Edges)
                    propagate(Src, Edge.Other, MatchState::FlowToWriteOnly, ReachSet, WorkList);
				for (auto &Edge : NodeInfo.ReverseEdges)
                    propagate(Src, Edge.Other, MatchState::FlowFromReadOnly, ReachSet, WorkList);
            }
			if(isPossiblyTainted(Val, NodeInfo.Attr)) {
			  //taint sources only propagate through toEdges
			  for (auto &Edge : NodeInfo.Edges)
                    propagate(Src, Edge.Other, MatchState::FlowToWriteOnly, ReachSet, WorkList);
              taintedBelow = true;
            }
        }
    }
  }
}

static Optional<InstantiatedValue> getNodeBelow(const CFLGraph &Graph,
                                                InstantiatedValue V) {
  auto NodeBelow = InstantiatedValue{V.Val, V.DerefLevel + 1};
  if (Graph.getNode(NodeBelow))
    return NodeBelow;
  return None;
}

static Optional<InstantiatedValue> getNodeAbove(const CFLGraph &Graph,
                                                InstantiatedValue V) {
  if (V.DerefLevel == 0)
    return None;
  auto NodeAbove = InstantiatedValue{V.Val, V.DerefLevel - 1};
  if (Graph.getNode(NodeAbove))
    return NodeAbove;
  return None;
}

static void matchLevelsChecked(CFLGraph &Graph, InstantiatedValue ToChange, const InstantiatedValue Target) {
  // if not limited by max level, 
  // deref levels may grow infinitely due to getelementptr 
  unsigned NewLevel = ToChange.DerefLevel + (Graph.getCurMaxLevel(Target.Val) - Target.DerefLevel);
  NewLevel = std::min(NewLevel, maxDerefLevel(ToChange.Val));
  Graph.addLevel(ToChange, NewLevel);
}

static void processWorkListItem(const WorkListItem &Item, CFLGraph &Graph,
                                ReachabilitySet &ReachSet, AliasMemSet &MemSet,
                                std::vector<WorkListItem> &WorkList) {
  auto FromNode = Item.From;
  auto ToNode = Item.To;
  auto NodeInfo = *const_cast<const CFLGraph&>(Graph).getNode(ToNode);
  //assert(NodeInfo != nullptr);

  // TODO: propagate field offsets

  // FIXME: Here is a neat trick we can do: since both ReachSet and MemSet holds
  // relations that are symmetric, we could actually cut the storage by half by
  // sorting FromNode and ToNode before insertion happens.

  // The newly added value alias pair may potentially generate more memory
  // alias pairs. Check for them here.
  auto FromNodeBelow = getNodeBelow(Graph, FromNode);
  auto ToNodeBelow = getNodeBelow(Graph, ToNode);
  //if the one node have more levels below, then the other node 
  //should have matching levels
 
  //if(ToNodeBelow && !FromNodeBelow) {
  //  matchLevelsChecked(Graph, FromNode, ToNode);
  //  FromNodeBelow = getNodeBelow(Graph, FromNode);
  //}
  //if(FromNodeBelow && !ToNodeBelow) {
  //  matchLevelsChecked(Graph, ToNode, FromNode);
  //  ToNodeBelow = getNodeBelow(Graph, ToNode);
  //}
  // FromNodeBelow and ToNodeBelow might still be none due to pointer level limits
  if(FromNodeBelow && ToNodeBelow && MemSet.insert(*FromNodeBelow, *ToNodeBelow)) {
    propagate(*FromNodeBelow, *ToNodeBelow, MatchState::FlowFromMemAliasNoReadWrite, 
  		ReachSet, WorkList);
    for (const auto &Mapping : ReachSet.reachableValueAliases(*FromNodeBelow)) {
      auto MemAliasPropagate = [&](MatchState FromState, MatchState ToState) {
		auto Src = Mapping.first;
        if (Mapping.second.test(static_cast<size_t>(FromState))) {
          propagate(Src, *ToNodeBelow, ToState, ReachSet, WorkList);
        }
      };
  
      MemAliasPropagate(MatchState::FlowFromReadOnly,
                        MatchState::FlowFromMemAliasReadOnly);
      MemAliasPropagate(MatchState::FlowToWriteOnly,
                        MatchState::FlowToMemAliasWriteOnly);
      MemAliasPropagate(MatchState::FlowToReadWrite,
                        MatchState::FlowToMemAliasReadWrite);
    }
  }

  // This is the core of the state machine walking algorithm. We expand ReachSet
  // based on which state we are at (which in turn dictates what edges we
  // should examine)
  // From a high-level point of view, the state machine here guarantees two
  // properties:
  // - If *X and *Y are memory aliases, then X and Y are value aliases
  // - If Y is an alias of X, then reverse assignment edges (if there is any)
  // should precede any assignment edges on the path from X to Y.
  auto NextAssignState = [&](MatchState State) {
    for (const auto &AssignEdge : NodeInfo.Edges)
      propagate(FromNode, AssignEdge.Other, State, ReachSet, WorkList);
  };
  auto NextRevAssignState = [&](MatchState State) {
    for (const auto &RevAssignEdge : NodeInfo.ReverseEdges)
      propagate(FromNode, RevAssignEdge.Other, State, ReachSet, WorkList);
  };
  auto NextMemState = [&](MatchState State) {
    if (auto AliasSet = MemSet.getMemoryAliases(ToNode)) {
      for (const auto &MemAlias : *AliasSet)
        propagate(FromNode, MemAlias, State, ReachSet, WorkList);
    }
  };

  switch (Item.State) {
  case MatchState::FlowFromReadOnly:
    NextRevAssignState(MatchState::FlowFromReadOnly);
    NextAssignState(MatchState::FlowToReadWrite);
    NextMemState(MatchState::FlowFromMemAliasReadOnly);
    break;

  case MatchState::FlowFromMemAliasNoReadWrite:
    NextRevAssignState(MatchState::FlowFromReadOnly);
    NextAssignState(MatchState::FlowToWriteOnly);
    break;

  case MatchState::FlowFromMemAliasReadOnly:
    NextRevAssignState(MatchState::FlowFromReadOnly);
    NextAssignState(MatchState::FlowToReadWrite);
    break;

  case MatchState::FlowToWriteOnly:
    NextAssignState(MatchState::FlowToWriteOnly);
    NextMemState(MatchState::FlowToMemAliasWriteOnly);
    break;

  case MatchState::FlowToReadWrite:
    NextAssignState(MatchState::FlowToReadWrite);
    NextMemState(MatchState::FlowToMemAliasReadWrite);
    break;

  case MatchState::FlowToMemAliasWriteOnly:
    NextAssignState(MatchState::FlowToWriteOnly);
    break;

  case MatchState::FlowToMemAliasReadWrite:
    NextAssignState(MatchState::FlowToReadWrite);
    break;
  }

  auto ToNodeAbove = getNodeAbove(Graph, ToNode); 
  if (notMemAliasState(Item.State) && ToNodeAbove) 
  {
	  auto NodeAboveInfo = *const_cast<const CFLGraph&>(Graph).getNode(*ToNodeAbove);
      for (const auto &Edge : NodeAboveInfo.Edges)
        propagate(*ToNodeAbove, Edge.Other, MatchState::FlowToWriteOnly, ReachSet,
                  WorkList);
      for (const auto &Edge : NodeAboveInfo.ReverseEdges)
        propagate(*ToNodeAbove, Edge.Other, MatchState::FlowFromReadOnly, ReachSet,
              WorkList);
      if (const auto AliasSet = MemSet.getMemoryAliases(*ToNodeAbove)) {
        for (const auto &MemAlias : *AliasSet)
            propagate(*ToNodeAbove, MemAlias, MatchState::FlowFromMemAliasNoReadWrite, ReachSet, WorkList);
    }
  }



}

static AliasAttrMap buildAttrMap(const CFLGraph &Graph,
                                 const ValueReachMap &RevReachMap) {
  AliasAttrMap AttrMap;
  std::vector<InstantiatedValue> WorkList, NextList;

  // Initialize each node with its original AliasAttrs in CFLGraph
  for (const auto &Mapping : Graph.value_mappings()) {
    auto Val = Mapping.first;
    auto &ValueInfo = Mapping.second;
    for (unsigned I = 0, E = ValueInfo.getNumLevels(); I < E; ++I) {
      auto Node = InstantiatedValue{Val, I};
      AttrMap.add(Node, ValueInfo.getNodeInfoAtLevel(I).Attr);
      WorkList.push_back(Node);
    }
  }

  while (!WorkList.empty()) {
    for (const auto &Src : WorkList) {
      auto SrcAttr = AttrMap.getAttrs(Src);
      if (SrcAttr.none())
        continue;

      // Propagate attr on the same level
      for (const auto &Mapping : RevReachMap.reachableValueAliases(Src)) {
        auto Dst = Mapping.first;
        if (AttrMap.add(Dst, SrcAttr)) {
          NextList.push_back(Dst);
		}
      }

      // Propagate attr to the levels below
      auto SrcBelow = getNodeBelow(Graph, Src);
	  auto Attr = maskTaintedAttr(SrcAttr);
      while (SrcBelow) {
        if (AttrMap.add(*SrcBelow, Attr)) {
          NextList.push_back(*SrcBelow);
          break;
        }
        SrcBelow = getNodeBelow(Graph, *SrcBelow);
      }
    }
    WorkList.swap(NextList);
    NextList.clear();
  }

  return AttrMap;
}

static TaintedSet buildTaintedVals(const CFLGraph &Graph,
                                   const AliasAttrMap &AttrMap) 
{
	TaintedSet TaintedVals;
	for (const auto &Mapping : Graph.value_mappings()) {
		auto Val = Mapping.first;
		auto &ValueInfo = Mapping.second;
		for (unsigned I = 0, E = ValueInfo.getNumLevels(); I < E; ++I) {
			auto Node = InstantiatedValue{Val, I};
			auto Attr = AttrMap.getAttrs(Node);
			if(isPossiblyTainted(Val, Attr)) {
				TaintedVals.insert(Node);
				//errs() << "add to tainted values" << Node << "\n";
			}
		}
	}
	return TaintedVals;
}


CFLAndersTaintResult::FunctionInfo
CFLAndersTaintResult::buildInfoFrom(const Function &Fn) {

  CFLGraphBuilder<CFLAndersTaintResult> GraphBuilder(
      *this, TLI,
      // Cast away the constness here due to GraphBuilder's API requirement
      const_cast<Function &>(Fn)
    );
  auto &Graph = GraphBuilder.getCFLGraph();

  ReachabilitySet ReachSet;
  AliasMemSet MemSet;

  std::vector<WorkListItem> WorkList, NextList;
  initializeWorkList(WorkList, ReachSet, Graph, GraphBuilder.getReturnValues());

  // TODO: make sure we don't stop before the fix point is reached
  while (!WorkList.empty()) {
    for (const auto &Item : WorkList)
      processWorkListItem(Item, Graph, ReachSet, MemSet, NextList);

    NextList.swap(WorkList);
    NextList.clear();
  }

  const ValueReachMap RevReachMap = ReachSet.getRevReachMap();
  // Now that we have all the reachability info, propagate AliasAttrs according
  // to it
  auto IValueAttrMap = buildAttrMap(Graph, RevReachMap);
  auto TaintedVals = buildTaintedVals(Graph, IValueAttrMap);

  auto FuncInfo = FunctionInfo(Fn, GraphBuilder.getReturnValues(), GraphBuilder.getVAArgs(), RevReachMap, std::move(IValueAttrMap), std::move(TaintedVals));

  FuncInfo.propagateExternalTaint(TaintedGlobalVars);
  FuncInfo.propagateExternalTaint(TaintedFormalArgs[&Fn]);
  propagateInterprocedural(FuncInfo) ;
  return FuncInfo;
}

void CFLAndersTaintResult::scan(const Function &Fn) {
  auto InsertPair = Cache.insert(std::make_pair(&Fn, Optional<FunctionInfo>()));
  (void)InsertPair;
  assert(InsertPair.second &&
         "Trying to scan a function that has already been cached");

  // Note that we can't do Cache[Fn] = buildSetsFrom(Fn) here: the function call
  // may get evaluated after operator[], potentially triggering a DenseMap
  // resize and invalidating the reference returned by operator[]  

  errs() << "------------------------------------------------------\n";
  errs() << "building info for " << getDemangledName(Fn) << "\n\n";
 
  auto FunInfo = buildInfoFrom(Fn);
  Cache[&Fn] = std::move(FunInfo);

  Handles.emplace_front(const_cast<Function *>(&Fn), this);
}

void CFLAndersTaintResult::evict(const Function *Fn) { Cache.erase(Fn); }

const Optional<CFLAndersTaintResult::FunctionInfo> &
CFLAndersTaintResult::ensureCached(const Function &Fn) {
  auto Iter = Cache.find(&Fn);
  if (Iter == Cache.end()) {
    scan(Fn);
    Iter = Cache.find(&Fn);
    assert(Iter != Cache.end());
    assert(Iter->second.hasValue());
  }
  return Iter->second;
}

const AliasSummary *CFLAndersTaintResult::getSummary(const Function &Fn) {
  auto &FunInfo = ensureCached(Fn);
  if (FunInfo.hasValue())
    return &FunInfo->getSummary();
  else
    return nullptr;
}

AliasResult CFLAndersTaintResult::query(const MemoryLocation &LocA,
                                     const MemoryLocation &LocB) {
  auto *ValA = LocA.Ptr;
  auto *ValB = LocB.Ptr;

  if (!ValA->getType()->isPointerTy() || !ValB->getType()->isPointerTy())
    return NoAlias;

  auto *Fn = parentFunctionOfValue(ValA);
  if (!Fn) {
    Fn = parentFunctionOfValue(ValB);
    if (!Fn) {
      // The only times this is known to happen are when globals + InlineAsm are
      // involved
      LLVM_DEBUG(
          dbgs()
          << "CFLAndersAA: could not extract parent function information.\n");
      return MayAlias;
    }
  } else {
    assert(!parentFunctionOfValue(ValB) || parentFunctionOfValue(ValB) == Fn);
  }

  assert(Fn != nullptr);
  auto &FunInfo = ensureCached(*Fn);

  // AliasMap lookup
  if (FunInfo->mayAlias(ValA, LocA.Size, ValB, LocB.Size))
    return MayAlias;
  return NoAlias;
}

AliasResult CFLAndersTaintResult::alias(const MemoryLocation &LocA,
                                     const MemoryLocation &LocB) {
  if (LocA.Ptr == LocB.Ptr)
    return MustAlias;

  // Comparisons between global variables and other constants should be
  // handled by BasicAA.
  // CFLAndersAA may report NoAlias when comparing a GlobalValue and
  // ConstantExpr, but every query needs to have at least one Value tied to a
  // Function, and neither GlobalValues nor ConstantExprs are.
  if (isa<Constant>(LocA.Ptr) && isa<Constant>(LocB.Ptr))
    return AAResultBase::alias(LocA, LocB);

  AliasResult QueryResult = query(LocA, LocB);
  if (QueryResult == MayAlias)
    return AAResultBase::alias(LocA, LocB);

  return QueryResult;
}

const Optional<std::vector<const Value *>> CFLAndersTaintResult::allValueAliases(const Value *V) {
  auto *Fn = parentFunctionOfValue(V);
  if (!Fn) { 
    // The only times this is known to happen are when globals + InlineAsm are
    // involved
    LLVM_DEBUG(
        dbgs()
        << "CFLAndersAA: could not extract parent function information.\n");
    return None;
  }
  auto &FunInfo = ensureCached(*Fn);
  if (FunInfo.hasValue())
    return FunInfo->getValueAliases(V); 
  else
    return None;
}

const Optional<DenseSet<const Value *>> CFLAndersTaintResult::taintedVals(const Function &Fn) {

  auto &FunInfo = ensureCached(Fn);
  if (FunInfo.hasValue()) {
    auto const TaintedSet = FunInfo->getTaintedVals();
	DenseSet<const Value *> vals;
    for(auto Itr = TaintedSet.begin(); Itr != TaintedSet.end(); Itr++) {
        if(Itr->DerefLevel == 0) {
            vals.insert(Itr->Val);
        }
    }
    return vals;
  }
  else
    return None;
}

const DenseMap<const Function*, DenseSet<const Value *>> CFLAndersTaintResult::taintedValsInReachableFuncs(const Function &Fn) {

  auto &FuncInfo = ensureCached(Fn);
  DenseMap<const Function*, DenseSet<const Value *>> valMap;
  if(!FuncInfo.hasValue())
	return valMap; 
  for (auto const &pair: Cache) {
	auto FuncInfo = pair.second;
	if (FuncInfo.hasValue()) {
		auto TaintedSet = FuncInfo->getTaintedVals();
		DenseSet<const Value *> vals;
		for(auto Itr = TaintedSet.begin(); Itr != TaintedSet.end(); Itr++) {
			if(Itr->DerefLevel == 0) {
				vals.insert(Itr->Val);
			}
		}
		valMap[pair.first] = vals;
	}	
  }
    return valMap;
}

AnalysisKey CFLAndersAA::Key;

CFLAndersTaintResult CFLAndersAA::run(Function &F, FunctionAnalysisManager &AM) {
  return CFLAndersTaintResult(AM.getResult<TargetLibraryAnalysis>(F));
}

char CFLAndersTaintWrapperPass::ID = 0;
static RegisterPass<CFLAndersTaintWrapperPass> X("cfl-anders-taint", "Inclusion-Based CFL Taint Analysis", false, true);


//INITIALIZE_PASS(CFLAndersTaintWrapperPass, "cfl-anders-taint",
//                "Inclusion-Based CFL Taint Analysis", false, true)


bool CFLAndersTaintWrapperPass::runOnModule(Module &M) {
    auto &TLIWP = getAnalysis<TargetLibraryInfoWrapperPass>();
	Result.reset(new CFLAndersTaintResult(TLIWP.getTLI()));
	for (auto FItr = M.begin(), FEnd = M.end(); FItr != FEnd;  FItr++) {
		Result->taintedVals(*FItr);
	}
	return true;
}

CFLAndersTaintWrapperPass::CFLAndersTaintWrapperPass() : ModulePass(ID) {
  //initializeCFLAndersTaintWrapperPassPass(*PassRegistry::getPassRegistry());
}

//void CFLAndersTaintWrapperPass::initializePass() {
//  auto &TLIWP = getAnalysis<TargetLibraryInfoWrapperPass>();
//  Result.reset(new CFLAndersTaintResult(TLIWP.getTLI()));
//}

void CFLAndersTaintWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<TargetLibraryInfoWrapperPass>();
}
