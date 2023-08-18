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
#include "PMConfig.h"

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
CFLGraph::CFLGraph() {}

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
	//  errs() << " add escaped attr to mutable " << N << "\n";

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
	//  errs() << " add escaped attr to mutable " << N << "\n";
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


  void CFLGraph::propagateLevels() {
    //TODO: deal with overflow
    struct WorkItem {
      Value *Val;
      int Deviation;
    };
    std::vector<WorkItem> WorkList;
    DenseSet<Value *> Done;
    for (auto &Pair: value_mappings()) {
      if (Done.count(Pair.first))
        continue;

      DenseMap<Value *, int>  DevMap;
      WorkList.push_back(WorkItem{Pair.first, 0});
      DevMap[Pair.first] = 0;

      while (!WorkList.empty()) {
        auto Item = WorkList.back();
        WorkList.pop_back();
        auto V = Item.Val;
        auto Dev = Item.Deviation;
        
        auto Itr = ValueImpls.find(V);
        assert(Itr != ValueImpls.end());
        auto &VInfo = Itr->second;
        unsigned Level = VInfo.getNumLevels();

        auto processNode = [&] (Node N, unsigned I) {
          int NewDev = Dev + (int)I - (int) N.DerefLevel;
          auto DItr = DevMap.find(N.Val);
          if(DItr == DevMap.end() || std::abs(NewDev) < std::abs(DItr->second)) {
            DevMap[N.Val] = NewDev;
            WorkList.push_back(WorkItem{N.Val, NewDev});
          }
        };

        for (unsigned I = 0; I < Level; I ++) {
          auto NInfo = VInfo.getNodeInfoAtLevel(I);
          for (auto &Edge : NInfo.Edges) 
	   	    processNode(Edge.Other, I);
          for (auto &Edge : NInfo.ReverseEdges)
            processNode(Edge.Other, I);
        }
      }    
      int Max = 0;
      for (auto &Pair: DevMap) {
        Max = std::max(Max, Pair.second + (int) getCurMaxLevel(Pair.first));
      }
    
      for (auto &Pair: DevMap) {
        unsigned FinalLevel = Max - Pair.second;
        addNode(Node{Pair.first, FinalLevel });
        //errs() << "final level for " << *Pair.first << " is " << FinalLevel << "\n";
        Done.insert(Pair.first);
      } 
    }
  }

} // end namespace cflta
} // end namespace llvm

