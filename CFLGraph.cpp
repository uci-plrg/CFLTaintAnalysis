//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
/// \file
/// This file defines CFLGraph, an auxiliary data structure used by CFL-based
/// alias analysis.
//
//===----------------------------------------------------------------------===//

#include "CFLGraph.h"
#include "CFLTaintAnalysisUtils.h"

namespace llvm {
namespace cflta {

/// The Program Expression Graph (PEG) of CFL analysis
/// CFLGraph is auxiliary data structure used by CFL-based alias analysis to
/// describe flow-insensitive pointer-related behaviors. Given an LLVM function,
/// the main purpose of this graph is to abstract away unrelated facts and
/// translate the rest into a form that can be easily digested by CFL analyses.
/// Each Node in the graph is an InstantiatedValue, and each edge represent a
/// pointer assignment between InstantiatedValue. Pointer
/// references/dereferences are not explicitly stored in the graph: we
/// implicitly assume that for each //node (X, I) it has a dereference edge to (X,
/// I+1) and a reference edge to (X, I-1).
CFLGraph::CFLGraph(const TargetLibraryInfo& TLI) : TLI(TLI){}

	bool CFLGraph::ValueInfo::addNodeToLevel(unsigned Level) {
      auto NumLevels = Levels.size();

      if (NumLevels > Level)
       return false;
      Levels.resize(Level + 1);
      return true;
    }

    CFLGraph::NodeInfo &CFLGraph::ValueInfo::getNodeInfoAtLevel(unsigned Level) {
      assert(Level < Levels.size());
      return Levels[Level];
    }
    const CFLGraph::NodeInfo &CFLGraph::ValueInfo::getNodeInfoAtLevel(unsigned Level) const {
      assert(Level < Levels.size());
      return Levels[Level];
    }

    unsigned CFLGraph::ValueInfo::getNumLevels() const { return Levels.size(); }

  CFLGraph::NodeInfo *CFLGraph::getNode(Node N) {
    auto Itr = ValueImpls.find(N.Val);
    if (Itr == ValueImpls.end() || Itr->second.getNumLevels() <= N.DerefLevel)
      return nullptr;
    return &Itr->second.getNodeInfoAtLevel(N.DerefLevel);
  }
  
  unsigned CFLGraph::getCurMaxLevel(const Value* Val) const { 
	auto Itr = ValueImpls.find(Val);
	assert(Itr != ValueImpls.end());
	return Itr->second.getNumLevels() - 1;
  }

  void CFLGraph::addLevel(Node N, unsigned Level) {
		
	//unsigned MaxLevels = maxDerefLevel(N.Val);
	
	// if not limited by max level, 
	// deref levels may grow infinitely due to getelementptr and bitcast
	//if (N.DerefLevel + 1 <MaxLevels) {
		addNode(Node{N.Val, Level}); 
	//}	
  }

  bool CFLGraph::addNode(Node N, AliasAttrs Attr)  {
    assert(N.Val != nullptr);
    auto &ValInfo = ValueImpls[N.Val];
    auto Changed = ValInfo.addNodeToLevel(N.DerefLevel);
    auto &NodeInfo = ValInfo.getNodeInfoAtLevel(N.DerefLevel);
    NodeInfo.Attr |= Attr;
    
	//if(hasTaintedAttr(Attr))
    //  errs() << " add tainted attr to " << N << "\n";
	//if(!isValueImmutable(N.Val) && hasUnknownAttr(Attr))
    //  errs() << " add unknown attr to mutable " << N << "\n";
	//if(!isValueImmutable(N.Val) && hasEscapedAttr(Attr))
	//  errs() << " add escpaed attr to mutable " << N << "\n";

    return Changed;
  }

  void CFLGraph::addAttr(Node N, AliasAttrs Attr) {
    auto *Info = getNode(N);
    assert(Info != nullptr);
    Info->Attr |= Attr;

	//if(hasTaintedAttr(Attr))
    //  errs() << " add tainted attr to " << N << "\n";
	//if(!isValueImmutable(N.Val) && hasUnknownAttr(Attr))
    //  errs() << " add unknown attr to mutable " << N << "\n";
	//if(!isValueImmutable(N.Val) && hasEscapedAttr(Attr))
	//  errs() << " add escpaed attr to mutable " << N << "\n";
  }

  void CFLGraph::addEdge(Node From, Node To, int64_t Offset) {
    auto *FromInfo = getNode(From);
    assert(FromInfo != nullptr);
    auto *ToInfo = getNode(To);
    assert(ToInfo != nullptr);

    FromInfo->Edges.push_back(Edge{To, Offset});
    ToInfo->ReverseEdges.push_back(Edge{From, Offset});

  }

  const CFLGraph::NodeInfo *CFLGraph::getNode(Node N) const {
    auto Itr = ValueImpls.find(N.Val);
    if (Itr == ValueImpls.end() || Itr->second.getNumLevels() <= N.DerefLevel)
      return nullptr;
    return &Itr->second.getNodeInfoAtLevel(N.DerefLevel);
  }

  AliasAttrs CFLGraph::attrFor(Node N) const {
    auto *Info = getNode(N);
    assert(Info != nullptr);
    return Info->Attr;
  }

  iterator_range<CFLGraph::const_value_iterator> CFLGraph::value_mappings() const {
    return make_range<const_value_iterator>(ValueImpls.begin(),
                                            ValueImpls.end());
  }


} // end namespace cflta
} // end namespace llvm

