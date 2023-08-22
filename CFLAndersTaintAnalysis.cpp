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

using namespace llvm;
using namespace llvm::cflta;

#define DEBUG_TYPE "cfl-anders-taint"

CFLAndersTaintResult::CFLAndersTaintResult(const TargetLibraryInfo &TLI) : TLI(TLI) {}
CFLAndersTaintResult::CFLAndersTaintResult(CFLAndersTaintResult &&RHS)
    : AAResultBase(std::move(RHS)), TLI(RHS.TLI) {}
CFLAndersTaintResult::~CFLAndersTaintResult() = default;

namespace {

const unsigned ReadOnlyStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowFromReadOnly)) |
    (1U << static_cast<uint8_t>(MatchState::FlowFromMemAliasReadOnly));
const unsigned WriteOnlyStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowToWriteOnly)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasWriteOnly));
const unsigned ReadWriteStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowToReadWrite)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasReadWrite));
const unsigned ReadStateMask =
    ReadOnlyStateMask | ReadWriteStateMask;    
const unsigned WriteStateMask =
    WriteOnlyStateMask | ReadWriteStateMask;    
const unsigned MemStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowFromMemAliasNoReadWrite)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasReadWrite)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasWriteOnly)) |
    (1U << static_cast<uint8_t>(MatchState::FlowFromMemAliasReadOnly));


static inline bool hasReadOnlyState(StateSet Set) {
  return (Set & StateSet(ReadOnlyStateMask)).any();
}

static inline bool hasWriteOnlyState(StateSet Set) {
  return (Set & StateSet(WriteOnlyStateMask)).any();
}

static inline bool hasReadWriteState(StateSet Set) {
  return (Set & StateSet(ReadWriteStateMask)).any();
}

static inline bool hasWriteState(StateSet Set) {
  return (Set & StateSet(WriteStateMask)).any();
}

static inline bool hasReadState(StateSet Set) {
  return (Set & StateSet(ReadStateMask)).any();
}

static inline bool hasNonWriteState(StateSet Set) {
  return (Set & ~StateSet(WriteStateMask)).any();
}

static inline bool hasNonReadState(StateSet Set) {
  return (Set & ~StateSet(ReadStateMask)).any();
}

static inline bool hasNonReadOnlyState(StateSet Set) {
  return (Set & ~StateSet(ReadOnlyStateMask)).any();
}

static inline bool hasNonMemAliasState(StateSet Set) {
  return (Set & ~StateSet(MemStateMask)).any();
}

static inline bool hasMemAliasWriteState(StateSet Set) {
  return (Set & StateSet(MemStateMask) & StateSet(WriteStateMask)).any();
}

static inline bool hasMemAliasNonWriteState(StateSet Set) {
  return (Set & StateSet(MemStateMask) & ~StateSet(WriteStateMask)).any();
}

static bool hasMemAliasNonReadState(StateSet Set) {
  return (Set & StateSet(MemStateMask) & ~StateSet(ReadStateMask)).any();
}

static const std::string StateNames[] = { "FlowFromReadOnly", "FlowFromMemAliasNoReadWrite", "FlowFromMemAliasReadOnly", "FlowToWriteOnly", "FlowToReadWrite", "FlowToMemAliasWriteOnly", "FlowToMemAliasReadWrite" };

raw_ostream &operator << ( raw_ostream& strm, MatchState ms )
{
   return strm << StateNames[(int)ms];
}

static inline Optional<MatchState> applyRead(MatchState State) {
  if(hasNonWriteState(toStateSet(State)))
    return MatchState::FlowFromReadOnly;
  return None;
}

static inline MatchState applyWrite(MatchState State) {
  if(hasReadState(toStateSet(State)))
    return MatchState::FlowToReadWrite;
  else
    return MatchState::FlowToWriteOnly;
}

static inline Optional<MatchState> applyMemAlias(MatchState State) {
  switch (State) {
    case MatchState::FlowFromReadOnly:
      return MatchState::FlowFromMemAliasReadOnly;
    case MatchState::FlowToWriteOnly:
      return MatchState::FlowToMemAliasWriteOnly;
    case MatchState::FlowToReadWrite:
      return MatchState::FlowToMemAliasReadWrite;
    default:
      return None;
  }
}

static inline StateSet composeStateSets(StateSet First, StateSet Second) {
   StateSet Res;

   if (hasNonWriteState(First) && Second.test(static_cast<uint8_t>(MatchState::FlowFromReadOnly)))
     Res.set(static_cast<uint8_t>(MatchState::FlowFromReadOnly));

   if (hasNonReadState(First) && Second.test(static_cast<uint8_t>(MatchState::FlowToWriteOnly)))
     Res.set(static_cast<uint8_t>(MatchState::FlowToWriteOnly));

   if ((hasReadState(First) && Second.test(static_cast<uint8_t>(MatchState::FlowToWriteOnly))) ||
       (hasReadOnlyState(First) && Second.test(static_cast<uint8_t>(MatchState::FlowToReadWrite))))
     Res.set(static_cast<uint8_t>(MatchState::FlowToReadWrite));

   if (First.test(static_cast<uint8_t>(MatchState::FlowFromReadOnly)) && hasMemAliasNonWriteState(Second))
     Res.set(static_cast<uint8_t>(MatchState::FlowFromMemAliasReadOnly));

   if (First.test(static_cast<uint8_t>(MatchState::FlowToWriteOnly)) && hasMemAliasNonReadState(Second))
     Res.set(static_cast<uint8_t>(MatchState::FlowToMemAliasWriteOnly));

   if ((First.test(static_cast<uint8_t>(MatchState::FlowFromReadOnly)) && hasMemAliasWriteState(Second)) ||
       (First.test(static_cast<uint8_t>(MatchState::FlowToReadWrite)) && hasMemAliasNonReadState(Second)))
     Res.set(static_cast<uint8_t>(MatchState::FlowToMemAliasReadWrite));

   return Res;
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
  ValueReachMap RevReachMap;
  ValueReachMap ReachMap;
public:
  using const_value_iterator = ValueReachMap::const_iterator;

  // Insert edge 'From->To' at state 'State'
  bool insert(InstantiatedValue From, InstantiatedValue To, MatchState State) {
    assert(From != To);
    auto &RevStates = RevReachMap[To][From];
    auto &States = ReachMap[From][To];
    auto Idx = static_cast<size_t>(State);
    if (!States.test(Idx)) {
      States.set(Idx);
      RevStates.set(Idx);
      return true;
    }
    return false;
  }

  // Return the set of all ('From', 'State') pair for a given node 'To'
  iterator_range<ValueStateMap::const_iterator> revReachableValueAliases(InstantiatedValue V) const {
    return RevReachMap.reachableValueAliases(V);
  }

  iterator_range<ValueStateMap::const_iterator> reachableValueAliases(InstantiatedValue V) const {
    return ReachMap.reachableValueAliases(V);
  }

  iterator_range<const_value_iterator> value_mappings() const {
    return make_range<const_value_iterator>(RevReachMap.begin(), RevReachMap.end());
  }

  const ValueReachMap &getReachMap() const {
	return ReachMap;
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

  ValueReachMap ReachMap;

  /// Map a value to its corresponding AliasAttrs
  DenseMap<const Value *, AliasAttrs> AttrMap;

  /// Summary of externally visible effects.
  AliasSummary Summary;

  Optional<AliasAttrs> getAttrs(const Value *) const;

public:
  FunctionInfo(const Function &, const ExternalVals&, 
			   const ValueReachMap &, const AliasAttrMap &, 
               const TaintedSet &);
  void propagateTaint(const TaintedSet&, TaintedSet *); 
  bool mayAlias(const Value *, LocationSize, const Value *, LocationSize) const;

  Optional<std::vector<const Value *>> getValueAliases(const Value *) const;

  const TaintedSet &getTaintedVals() const { return TaintedVals; }
  const DenseMap<const Value *, AliasAttrs> &getAttrMap() const { return AttrMap; }
  const AliasSummary &getSummary() const { return Summary; }
  const ValueReachMap &getReachMap() const { return ReachMap; }
 
};

static Optional<InterfaceValue>
getInterfaceValue(InstantiatedValue IValue,
				  const Function &Fn,
                  const ExternalVals &ExtVals) {
  //Globals are handled in getGlobalInterfaceValue
  auto Val = IValue.Val;

  Optional<unsigned> Index;
  auto ArgSize = Fn.arg_size();
  if (auto Arg = dyn_cast<Argument>(Val))
    Index = Arg->getArgNo() + 1;
  else if (is_contained(ExtVals.VAArgs, Val))
	Index = ArgSize + 1;
  else if (is_contained(ExtVals.RetVals, Val))
    Index = 0;

  if (Index)
    return InterfaceValue{*Index, IValue.DerefLevel};
  return None;
}

static bool
isExternalValue(const Value *Val,
                 const ExternalVals &ExtVals) {
  bool Ret = false;
  if (isa<Argument>(Val) || 
      is_contained(ExtVals.VAArgs, Val) || 
      is_contained(ExtVals.RetVals, Val))
    Ret = true;
  if (auto GVar = dyn_cast<GlobalVariable>(Val)) 
    if (!GVar->isConstant())
      Ret = true;

  return Ret;
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
                 const ValueReachMap &ReachMap) {
  for (const auto &OuterMapping : ReachMap) {
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

static void populateExternalRelations(
    SmallVectorImpl<ExternalRelation> &ExtRelations, const Function &Fn,
    const ExternalVals &ExtVals,
	const ValueReachMap &ReachMap) {
  // If a function only returns one of its argument X, then X will be both an
  // argument and a return value at the same time. This is an edge case that
  // needs special handling here.
  for (const auto &Arg : Fn.args()) {
    if (is_contained(ExtVals.RetVals, &Arg)) {
      auto ArgVal = InterfaceValue{Arg.getArgNo() + 1, 0};
      auto RetVal = InterfaceValue{0, 0};
      ExtRelations.push_back(ExternalRelation{ArgVal, RetVal, 0});
    }
  }

 //the case where the function returns a variadic argument
 for (const auto *Arg: ExtVals.VAArgs) {
	if (is_contained(ExtVals.RetVals, Arg)) {
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
  for (const auto &OuterMapping : ReachMap) {
    if (auto Src = getInterfaceValue(OuterMapping.first, Fn, ExtVals)) {
      for (const auto &InnerMapping : OuterMapping.second) {
        // If Src is a param/return value, we get a same-level assignment.
        if (auto Dst = getInterfaceValue(InnerMapping.first, Fn, ExtVals)) {
          
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
    const ExternalVals &ExtVals, const AliasAttrMap &AMap) {
  for (const auto &Mapping : AMap.mappings()) {
    if (auto IVal = getInterfaceValue(Mapping.first, Fn, ExtVals)) {
      auto Attr = getExternallyVisibleAttrs(Mapping.second);
      if (Attr.any())
        ExtAttributes.push_back(ExternalAttribute{*IVal, Attr});
    }	
  }
}

static StateSet ExternalTaintShim(const StateSet &States) {
  auto Ret = States;
  if (Ret.test(static_cast<uint8_t>(MatchState::FlowFromMemAliasReadOnly)) || 
      Ret.test(static_cast<uint8_t>(MatchState::FlowFromMemAliasNoReadWrite))) {
    Ret.set(static_cast<uint8_t>(MatchState::FlowFromReadOnly));
  }
  if (Ret.test(static_cast<uint8_t>(MatchState::FlowToMemAliasWriteOnly))) {
    Ret.set(static_cast<uint8_t>(MatchState::FlowToWriteOnly));
  }
  if (Ret.test(static_cast<uint8_t>(MatchState::FlowToMemAliasReadWrite))) {
    Ret.set(static_cast<uint8_t>(MatchState::FlowToReadWrite));
  }
  Ret = Ret & ~StateSet(MemStateMask);
  return Ret;
}

static void populateExternalTaints(
    SmallVectorImpl<ExternalTaint> &ExtTaints, const Function &Fn,
    const ExternalVals &ExtVals, const TaintedSet &TaintedVals) {
  for (const auto &Mapping : TaintedVals) {
    if (auto IVal = getInterfaceValue(Mapping.first, Fn, ExtVals)) {
      auto ExternalTaintStates = ExternalTaintShim(Mapping.second);
      ExtTaints.push_back(ExternalTaint{*IVal, ExternalTaintStates});
      //errs() << "added to external taint " << *IVal << " with " << ExternalTaintStates.to_string() << "\n"; 
    }	
  }
}

void CFLAndersTaintResult::FunctionInfo::propagateTaint(const TaintedSet &TaintSources, TaintedSet* NewTaints = nullptr) {
  
  for(auto &Mapping: TaintSources) {
    auto IVal = Mapping.first;
    auto NewTaintStates = TaintedVals.addStates(IVal, Mapping.second);
    if(NewTaintStates.any()) {
      if(NewTaints)
        NewTaints->addStates(IVal, NewTaintStates);
      //errs() << "taint source " << IVal << " with " << NewTaintStates.to_string() << "\n";
      auto Aliases = ReachMap.reachableValueAliases(IVal);
      for(auto &AliasMapping: Aliases) {
        auto AliasIVal = AliasMapping.first;
        auto NewTaintStates2 = composeStateSets(NewTaintStates, AliasMapping.second);
        if(NewTaintStates2.any()) {
          auto NewTaintStates3 = TaintedVals.addStates(AliasIVal, NewTaintStates2);
          if(NewTaintStates3.any()) {			
            if(NewTaints) 
          	NewTaints->addStates(AliasIVal, NewTaintStates3);
            //errs() << "alias of taint source " << AliasIVal << " with new states " << NewTaintStates3.to_string() << "\n";
          }
        }
      }
 
      //expand out mem aliases not explored when processing intraprocedurally
      //TODO: should Dec be incremented to <= IVal.DerefLevel? should ExpMapping be added to TaintedVals?
      if (NewTaints && Aliases.begin() == Aliases.end()) {
        for (unsigned Dec = 1; Dec <= IVal.DerefLevel; Dec++) {
          for(auto &ExpMapping: ReachMap.reachableValueAliases(InstantiatedValue{IVal.Val, IVal.DerefLevel - Dec})) {
            auto ExpIVal = InstantiatedValue{ExpMapping.first.Val, ExpMapping.first.DerefLevel + Dec};
            if(ExpIVal.DerefLevel > maxDerefLevel(ExpIVal.Val))
              continue;
            
            auto MemNoReadWrite = toStateSet(MatchState::FlowFromMemAliasNoReadWrite);
            if(NewTaints->addStates(ExpIVal, MemNoReadWrite).any()) {
        	  //errs() << "expanded alias of taint source " << ExpIVal << "\n";
            }
      	  }
        }
      }
    }
  }
}

CFLAndersTaintResult::FunctionInfo::FunctionInfo(
    const Function &Fn, const ExternalVals &ExtVals, 
	const ValueReachMap &ReachMap, const AliasAttrMap &AMap, 
    const TaintedSet &TaintSources): ReachMap(ReachMap) {
  populateAttrMap(AttrMap, AMap);
  populateExternalAttributes(Summary.RetParamAttributes, Fn, ExtVals, AMap);
  populateAliasMap(AliasMap, ReachMap);
  populateExternalRelations(Summary.RetParamRelations, Fn, ExtVals, ReachMap);
  propagateTaint(TaintSources);
  populateExternalTaints(Summary.RetParamTaints, Fn, ExtVals, TaintedVals);
}

void CFLAndersTaintResult::InterprocTaintInfo::collectNewTaints (const TaintedSet &TaintedVals) {
  NewTaintMap.clear();
  for (const auto &Mapping : TaintedVals) {
    auto IVal = Mapping.first;					
	for(const auto &Use : IVal.Val->uses()) {
		if(const auto Call = dyn_cast<CallInst>(Use.getUser())) {
			//arguments are the operands at the beginning in a CallInst
			if(!Call->isArgOperand(&Use))
				continue;
			auto Callee = Call->getCalledFunction();
		    // TODO: If the call is indirect, we might be need to enumerate all
		    // potential callees
			if(!Callee)
				continue;
			unsigned ArgNum = CallSite(Call).getArgumentNo(&Use);
			if(Callee->isVarArg() && ArgNum >= Callee->arg_size())
				continue;
			auto IArg = InstantiatedValue{Callee->arg_begin() + ArgNum, IVal.DerefLevel};
            auto NewTaintStates = TaintedFuncArgsGlobals[Callee].addStates(IArg, Mapping.second);
			if(NewTaintStates.any()) {
			  NewTaintMap[Callee].addStates(IArg, NewTaintStates);
				//errs() << "propagate formal argument taint from " << IVal << " to " << IArg << " to function " << Callee->getName() << "\n";
            }
		}

	}

	if(isa<GlobalVariable>(IVal.Val)) { 
      auto NewTaintStates = TaintedGlobalVars.addStates(IVal, Mapping.second);
	  if (NewTaintStates.any()) {
		for(const auto &Use : IVal.Val->uses()) {
			if(auto Inst = dyn_cast<Instruction>(Use.getUser())) {
				auto Func = Inst->getFunction();
                if(!Func)
                  continue;
                TaintedFuncArgsGlobals[Func].addStates(IVal, NewTaintStates);
			    NewTaintMap[Func].addStates(IVal, NewTaintStates);
				//errs() << "propagate global taint to " << IVal << " in function " << Func->getName() << "\n";
			}
		}
	  }
    }
  }
}

void CFLAndersTaintResult::propagateInterprocTaint(const Function &Fn) {
    auto Itr = Cache.find(&Fn); 
    assert(Itr != Cache.end() && Itr->second);
    auto &FuncInfo = *Itr->second; 
    FuncInfo.propagateTaint(ITI.TaintedFuncArgsGlobals[&Fn]);
	ITI.collectNewTaints(FuncInfo.getTaintedVals());

	while(!ITI.NewTaintMap.empty()) {
		TaintedSet NewTaints;
		for (const auto &Pair: ITI.NewTaintMap) {
			Itr = Cache.find(Pair.first); 
			if(Itr != Cache.end() && Itr->second) {
				//errs() << "propagate external taint to " << Pair.first->getName() << "\n";
			    Itr->second->propagateTaint(Pair.second, &NewTaints);
			}
		}
        ITI.collectNewTaints(NewTaints);
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
    if(isa<ConstantPointerNull>(To.Val))
		return;
    WorkList.push_back(WorkListItem{From, To, State});
  }

}

static void initializeWorkList(std::vector<WorkListItem> &WorkList,
                               ReachabilitySet &ReachSet,
                               const CFLGraph &Graph,
                               const ExternalVals &ExtVals,
                               const TaintedSet &TaintedVals) {
  for (const auto &Mapping : Graph.value_mappings()) {
    auto Val = Mapping.first;
    auto &ValueInfo = Mapping.second;
    assert(ValueInfo.getNumLevels() > 0);
   
	//values with possible external effects 
    if (isExternalValue(Val, ExtVals)) {
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
      unsigned LowerBound = 0;
      for (unsigned I = 0, E = ValueInfo.getNumLevels(); I < E; I++) {
        if (TaintedVals.count(InstantiatedValue{Val, I}))
          LowerBound = I + 1;
      }
      for (unsigned I = 0; I < LowerBound; I++) {
        auto Src = InstantiatedValue{Val, I};
	    auto NodeInfo = ValueInfo.getNodeInfoAtLevel(I);
        for (auto &Edge : NodeInfo.Edges)
          propagate(Src, Edge.Other, MatchState::FlowToWriteOnly, ReachSet, WorkList);
        for (auto &Edge : NodeInfo.ReverseEdges)
          propagate(Src, Edge.Other, MatchState::FlowFromReadOnly, ReachSet,WorkList);
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

static void processWorkListItem(const WorkListItem &Item, CFLGraph &Graph,
                                ReachabilitySet &ReachSet, AliasMemSet &MemSet,
                                std::vector<WorkListItem> &WorkList,
                                const ExternalVals &ExtVals) {
  auto FromNode = Item.From;
  auto ToNode = Item.To;
  const auto ConstGraph = const_cast<const CFLGraph&>(Graph);
  auto NodeInfo = ConstGraph.getNode(ToNode);
  assert(NodeInfo != nullptr);
  
  //errs() << "item from " << Item.From << " to " << Item.To << " with " << Item.State << "\n";

  // FIXME: Here is a neat trick we can do: since both ReachSet and MemSet holds
  // relations that are symmetric, we could actually cut the storage by half by
  // sorting FromNode and ToNode before insertion happens.

  // The newly added value alias pair may potentially generate more memory
  // alias pairs. Check for them here. 
    
  auto FromNodeBelow = getNodeBelow(Graph, FromNode);
  auto ToNodeBelow = getNodeBelow(Graph, ToNode);
  if(ToNodeBelow && !FromNodeBelow && isExternalValue(FromNode.Val, ExtVals) &&
       FromNode.DerefLevel < maxDerefLevel(FromNode.Val)) {
     FromNodeBelow = InstantiatedValue{FromNode.Val, FromNode.DerefLevel + 1};
     //errs() << "add level to FromNode " << FromNode << " due to " << ToNode << " with " << Item.State << "\n";
     Graph.addNode(*FromNodeBelow);
  } 
  else if (FromNodeBelow && !ToNodeBelow && 
       ToNode.DerefLevel < maxDerefLevel(ToNode.Val)) {
     ToNodeBelow = InstantiatedValue{ToNode.Val, ToNode.DerefLevel + 1};
     //errs() << "add level to ToNode " << ToNode << " due to " << FromNode << " with " << Item.State << "\n";
     Graph.addNode(*ToNodeBelow);
  }

  
  if(FromNodeBelow && ToNodeBelow && MemSet.insert(*FromNodeBelow, *ToNodeBelow)) {
    propagate(*FromNodeBelow, *ToNodeBelow, MatchState::FlowFromMemAliasNoReadWrite, 
  		ReachSet, WorkList);
    for (const auto &Mapping : ReachSet.revReachableValueAliases(*FromNodeBelow)) {
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
    for (const auto &AssignEdge : NodeInfo->Edges)
        propagate(FromNode, AssignEdge.Other, State, ReachSet, WorkList);
  };
  auto NextRevAssignState = [&](MatchState State) {
    for (const auto &RevAssignEdge : NodeInfo->ReverseEdges)
        propagate(FromNode, RevAssignEdge.Other, State, ReachSet, WorkList);
  };
  auto NextMemState = [&](MatchState State) {
    if (auto AliasSet = MemSet.getMemoryAliases(ToNode)) {
      for (const auto &MemAlias : *AliasSet)
        propagate(FromNode, MemAlias, State, ReachSet, WorkList);
    }
  };

  auto AfterRead = applyRead(Item.State);
  if(AfterRead)
    NextRevAssignState(*AfterRead);

  NextAssignState(applyWrite(Item.State));

  auto AfterMem = applyMemAlias(Item.State);
  if(AfterMem)
    NextMemState(*AfterMem);

  auto ToNodeAbove = getNodeAbove(Graph, ToNode);
  if (hasNonMemAliasState(toStateSet(Item.State)) && ToNodeAbove) 
  {
	auto NodeAboveInfo = ConstGraph.getNode(*ToNodeAbove);
    for (const auto &Edge : NodeAboveInfo->Edges)
      propagate(*ToNodeAbove, Edge.Other, MatchState::FlowToWriteOnly, ReachSet,
        WorkList);
    for (const auto &Edge : NodeAboveInfo->ReverseEdges) {
      propagate(*ToNodeAbove, Edge.Other, MatchState::FlowFromReadOnly, ReachSet,
        WorkList);
    }
    if (const auto AliasSet = MemSet.getMemoryAliases(*ToNodeAbove)) {
      for (const auto &MemAlias : *AliasSet)
        propagate(*ToNodeAbove, MemAlias, MatchState::FlowFromMemAliasNoReadWrite, ReachSet, WorkList);
    }
  }



}

static AliasAttrMap buildAttrMap(const CFLGraph &Graph,
                                 const ValueReachMap &ReachMap) {
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
      for (const auto &Mapping : ReachMap.reachableValueAliases(Src)) {
        auto Dst = Mapping.first;
		auto Attr = hasNonReadOnlyState(Mapping.second)? SrcAttr : maskTaintedAttr(SrcAttr);
        if (AttrMap.add(Dst, Attr)) {
          NextList.push_back(Dst);
		}
      }

      // Propagate attr to the levels below
      auto SrcBelow = getNodeBelow(Graph, Src);
	  SrcAttr = maskTaintedAttr(SrcAttr);
      while (SrcBelow) {
        if (AttrMap.add(*SrcBelow, SrcAttr)) {
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

CFLAndersTaintResult::FunctionInfo
CFLAndersTaintResult::buildInfoFrom(const Function &Fn) {  
  //errs() << "------------------------------------------------------\n";
  //errs() << "building graph for " << getDemangledName(Fn) << "\n\n";
  CFLGraphBuilder<CFLAndersTaintResult> GraphBuilder(
      *this, TLI,
      // Cast away the constness here due to GraphBuilder's API requirement
      const_cast<Function &>(Fn)
    );
  //errs() << "------------------------------------------------------\n";
  //errs() << "building info for " << getDemangledName(Fn) << "\n\n";
  //errs() << Fn << "\n";
  auto &Graph = GraphBuilder.getCFLGraph();
  auto TaintedSources = Graph.getTainted();
 
  ReachabilitySet ReachSet;
  AliasMemSet MemSet;

  std::vector<WorkListItem> WorkList, NextList;
  initializeWorkList(WorkList, ReachSet, Graph, GraphBuilder.getExternalVals(), TaintedSources);

  // TODO: make sure we don't stop before the fix point is reached
  while (!WorkList.empty()) {
    for (const auto &Item : WorkList)
      processWorkListItem(Item, Graph, ReachSet, MemSet, NextList, GraphBuilder.getExternalVals());

    NextList.swap(WorkList);
    NextList.clear();
  }

  const ValueReachMap ReachMap = ReachSet.getReachMap();
  // Now that we have all the reachability info, propagate AliasAttrs according
  // to it
  auto IValueAttrMap = buildAttrMap(Graph, ReachMap);

  auto FuncInfo = FunctionInfo(Fn, GraphBuilder.getExternalVals(), ReachMap, std::move(IValueAttrMap), TaintedSources);

  //errs() << "------------------------------------------------------\n";
  //errs() << "finish building " << getDemangledName(Fn) << "\n\n";
  //errs() << Fn << "\n";
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

 
  auto FunInfo = buildInfoFrom(Fn);
  Cache[&Fn] = std::move(FunInfo);
  propagateInterprocTaint(Fn);

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

/*
const static std::string FuncWithSelfLoop[] = {"free_node", "find_successor", "ctl_delete_indexes", "ctl_find_node", "pmalloc_boot", "palloc_defrag", "palloc_heap_action_on_cancel", "palloc_heap_action_on_unlock", "heap_buckets_init", "heap_arena_new","heap_create_alloc_class_buckets", "critnib_remove", "critnib_insert", "critnib_delete", "alloc_node", "free_leaf", "alloc_leaf", "obj_replica_init", "obj_rep_persist","obj_rep_flush","obj_rep_drain", "obj_rep_memcpy", "obj_rep_memmove", "obj_rep_memset", "obj_pool_lock_cleanup",  "obj_open_common", "obj_runtime_init", "obj_cleanup_remote", "pmemobj_createU", "util_pool_create_uuids", "util_range_find_unlocked", "util_poolset_directory_load","util_range_register","util_range_split", "lane_info_delete", "lane_init", "lane_info_cleanup", "get_lane_info_record", "operation_add_typed_entry", "ravl_node_type_most", "ravl_node_successor", "ravl_node_cessor", "ravl_find", "ravl_remove", "ravl_node_ref", "container_ravl_get_rm_block_bestfit", "ravl_rotate", "ravl_rotate", "ravl_balance", "ravl_emplace", "heap_run_reuse", "heap_ensure_run_bucket_filled", "memblock_run_init", "add_to_tx_and_lock", "pmemobj_tx_begin", "tx_alloc_common", "tx_remove_range","tx_restore_range", "release_and_free_tx_locks", "operation_add_buffer", "list_insert_new", "pmemobj_reserve", "pmemobj_xreserve", "check_domain_in_region", "pmem2_auto_flush"};
*/

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

Optional<DenseSet<Value *>> CFLAndersTaintResult::taintedVals(const Function &Fn) {

  auto &FunInfo = ensureCached(Fn);
  if (FunInfo.hasValue()) {
    auto TSet = FunInfo->getTaintedVals();
	DenseSet<Value *> Vals;
    for(const auto &Mapping: TSet) {
        auto IVal = Mapping.first;
        if(IVal.DerefLevel == 0) {
            Vals.insert(IVal.Val);
        }
    }
    return Vals;
  }
  else
    return None;
}

DenseMap<const Function*, DenseSet<Value *>> CFLAndersTaintResult::taintedValsInReachableFuncs(const Function &Fn) {

  auto &FuncInfo = ensureCached(Fn);
  DenseMap<const Function *, DenseSet<Value *>> ValMap;
  if(!FuncInfo.hasValue())
	return ValMap; 
  for (auto const &Pair: Cache) {
	auto FuncInfo = Pair.second;
	auto Vals = taintedVals(*Pair.first);
	if (Vals)
		ValMap[Pair.first] = *Vals;
  }
    return ValMap;
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
	  //if(FItr->getName().equals(StringRef("main")))
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
