#ifndef LLVM_LIB_ANALYSIS_TAINT_CFLGRAPH_BUILDER_H
#define LLVM_LIB_ANALYSIS_TAINT_CFLGRAPH_BUILDER_H

#include "AliasAnalysisSummary.h"
#include "CFLGraph.h"
#include "KnownFunctions.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include <cxxabi.h>
#include <cassert>
#include <cstdint>
#include <functional>
#include <vector>

namespace llvm {
namespace cflta {

using namespace PatternMatch;

///A builder class used to create CFLGraph instance from a given function
/// The CFL-AA that uses this builder must provide its own type as a template
/// argument. This is necessary for interprocedural processing: CFLGraphBuilder
/// needs a way of obtaining the summary of other functions when callinsts are
/// encountered.
/// As a result, we expect the said CFL-AA to expose a getSummary() public
/// member function that takes a Function& and returns the corresponding summary
/// as a const AliasSummary*.
template <typename CFLAA> class CFLGraphBuilder {
  // Input of the builder
  CFLAA &Analysis;
  const TargetLibraryInfo &TLI;
  SmallVector<Value *, 4> &GlobalVars;
  const bool IsVarArg;

  // Output of the builder
  CFLGraph Graph;
  SmallVector<Value *, 4> ReturnedValues;
  SmallVector<Value *, 4> VAArgs;

  // Helper class
  /// Gets the edges our graph should have, based on an Instruction*
  class GetEdgesVisitor : public InstVisitor<GetEdgesVisitor, void> {
    CFLAA &AA;
    const DataLayout &DL;
    const TargetLibraryInfo &TLI;
	SmallVector<Value *, 4> &GlobalVars;
    const bool IsVarArg;

    CFLGraph &Graph;
    SmallVectorImpl<Value *> &ReturnValues;
	SmallVector<Value *, 4> &VAArgs;

    static bool hasUsefulEdges(ConstantExpr *CE) {
      // ConstantExpr doesn't have terminators, invokes, or fences, so only
      // needs
      // to check for compares.
      return CE->getOpcode() != Instruction::ICmp &&
             CE->getOpcode() != Instruction::FCmp;
    }

    // Returns possible functions called by CS into the given SmallVectorImpl.
    // Returns true if targets found, false otherwise.
    static bool getPossibleTargets(CallSite CS,
                                   SmallVectorImpl<Function *> &Output) {
      if (auto *Fn = CS.getCalledFunction()) {
        Output.push_back(Fn);
        return true;
      }

      // TODO: If the call is indirect, we might be able to enumerate all
      // potential
      // targets of the call and return them, rather than just failing.
      return false;
    }

    void addNode(Value *Val, AliasAttrs Attr = AliasAttrs()) {
      assert(Val != nullptr && Val->getType()->isPointerTy());
      if (auto GVal = dyn_cast<GlobalValue>(Val)) {
        if (Graph.addNode(InstantiatedValue{GVal, 0},
                          getGlobalOrArgAttrFromValue(*GVal))) {
          //Graph.addNode(InstantiatedValue{GVal, 1}, getAttrUnknown());
		  auto IV = InstantiatedValue{GVal, 1};
		  Graph.addNode(IV);
		  if (auto GVar = dyn_cast<GlobalVariable>(GVal)) {
		    if (!GVar->hasInitializer() || !GVar->hasDefinitiveInitializer())
			  Graph.addNode(IV, getAttrUnknown());
		  }
		}
      } else if (auto CExpr = dyn_cast<ConstantExpr>(Val)) {
        if (hasUsefulEdges(CExpr)) {
          if (Graph.addNode(InstantiatedValue{CExpr, 0}))
            visitConstantExpr(CExpr);
        }
      } else
        Graph.addNode(InstantiatedValue{Val, 0}, Attr);
    }

    void addAssignEdge(Value *From, Value *To, int64_t Offset = 0) {
      assert(From != nullptr && To != nullptr);
      if (!From->getType()->isPointerTy() || !To->getType()->isPointerTy())
        return;
      addNode(From);
      if (To != From) {
        addNode(To);
        Graph.addEdge(InstantiatedValue{From, 0}, InstantiatedValue{To, 0},
                      Offset);
      }
    }

    //a store pattern used in std::atomic functions
    //ty** From, To;
	//int Val;
	//int* , Ptr0, Ptr;
	//Ptr0 = bitcast From;
	//Ptr = bitcast To;
    //Val = load Ptr0;
	//store Val Ptr;
	void handleCastToIntAndStore(const Value *Val, const Value *Ptr) {
		if (!Val->getType()->isIntegerTy() || !Ptr->getType()->isPointerTy())
			return;
		Value *From, *To;
		if(match(Val, m_Load(m_BitCast(m_Value(From)))) &&
		   match(Ptr, m_BitCast(m_Value(To))) && 
		   maxDerefLevel(From) > 1 &&
		   maxDerefLevel(To) > 1) {
			Graph.addNode(InstantiatedValue{From, 1});
			Graph.addNode(InstantiatedValue{To, 1});
			Graph.addEdge(InstantiatedValue{From, 1}, InstantiatedValue{To, 1});
		}
	}

    void addDerefEdge(Value *From, Value *To, bool IsRead) {
      assert(From != nullptr && To != nullptr);
      // FIXME: This is subtly broken, due to how we model some instructions
      // (e.g. extractvalue, extractelement) as loads. Since those take
      // non-pointer operands, we'll entirely skip adding edges for those.
      //
      // addAssignEdge seems to have a similar issue with insertvalue, etc.
      if (!From->getType()->isPointerTy() || !To->getType()->isPointerTy()) {
		if(!IsRead)
			handleCastToIntAndStore(From, To);
        return;
	  }
      addNode(From);
      addNode(To);
      if (IsRead) {
        Graph.addNode(InstantiatedValue{From, 1});
        Graph.addEdge(InstantiatedValue{From, 1}, InstantiatedValue{To, 0});
      } else {
        Graph.addNode(InstantiatedValue{To, 1});
        Graph.addEdge(InstantiatedValue{From, 0}, InstantiatedValue{To, 1});
      }
    }

    void addLoadEdge(Value *From, Value *To) { addDerefEdge(From, To, true); }
    void addStoreEdge(Value *From, Value *To) { addDerefEdge(From, To, false); }

  public:
    GetEdgesVisitor(CFLGraphBuilder &Builder, const DataLayout &DL)
        : AA(Builder.Analysis), DL(DL), TLI(Builder.TLI), GlobalVars(Builder.GlobalVars), IsVarArg(Builder.IsVarArg) , Graph(Builder.Graph), ReturnValues(Builder.ReturnedValues), VAArgs(Builder.VAArgs){}

    void visitInstruction(Instruction &) {
      llvm_unreachable("Unsupported instruction encountered");
    }

    void visitReturnInst(ReturnInst &Inst) {
      if (auto RetVal = Inst.getReturnValue()) {
        if (RetVal->getType()->isPointerTy()) {
          addNode(RetVal);
          ReturnValues.push_back(RetVal);
        }
      }
    }

    void visitPtrToIntInst(PtrToIntInst &Inst) {
      auto *Ptr = Inst.getOperand(0);
      addNode(Ptr, getAttrEscaped());
    }

    void visitIntToPtrInst(IntToPtrInst &Inst) {
      auto *Ptr = &Inst;
      addNode(Ptr, getAttrUnknown());
    }

    void visitCastInst(CastInst &Inst) {
      auto *Src = Inst.getOperand(0);
      addAssignEdge(Src, &Inst);
    }

    void visitBinaryOperator(BinaryOperator &Inst) {
      auto *Op1 = Inst.getOperand(0);
      auto *Op2 = Inst.getOperand(1);
      addAssignEdge(Op1, &Inst);
      addAssignEdge(Op2, &Inst);
    }

    void visitAtomicCmpXchgInst(AtomicCmpXchgInst &Inst) {
      auto *Ptr = Inst.getPointerOperand();
      auto *Val = Inst.getNewValOperand();
      addStoreEdge(Val, Ptr);
    }

    void visitAtomicRMWInst(AtomicRMWInst &Inst) {
      auto *Ptr = Inst.getPointerOperand();
      auto *Val = Inst.getValOperand();
      addStoreEdge(Val, Ptr);
    }

    void visitPHINode(PHINode &Inst) {
      for (Value *Val : Inst.incoming_values())
        addAssignEdge(Val, &Inst);
    }

    void visitGEP(GEPOperator &GEPOp) {
      uint64_t Offset = UnknownOffset;
      APInt APOffset(DL.getPointerSizeInBits(GEPOp.getPointerAddressSpace()),
                     0);
      if (GEPOp.accumulateConstantOffset(DL, APOffset))
        Offset = APOffset.getSExtValue();

      auto *Op = GEPOp.getPointerOperand();
      addAssignEdge(Op, &GEPOp, Offset);
    }

    void visitGetElementPtrInst(GetElementPtrInst &Inst) {
      auto *GEPOp = cast<GEPOperator>(&Inst);
      visitGEP(*GEPOp);
    }

    void visitSelectInst(SelectInst &Inst) {
      // Condition is not processed here (The actual statement producing
      // the condition result is processed elsewhere). For select, the
      // condition is evaluated, but not loaded, stored, or assigned
      // simply as a result of being the condition of a select.

      auto *TrueVal = Inst.getTrueValue();
      auto *FalseVal = Inst.getFalseValue();
      addAssignEdge(TrueVal, &Inst);
      addAssignEdge(FalseVal, &Inst);
    }

    void visitAllocaInst(AllocaInst &Inst) { addNode(&Inst); }

    void visitLoadInst(LoadInst &Inst) {
      auto *Ptr = Inst.getPointerOperand();
      auto *Val = &Inst;
      addLoadEdge(Ptr, Val);
    }

    void visitStoreInst(StoreInst &Inst) {
      auto *Ptr = Inst.getPointerOperand();
      auto *Val = Inst.getValueOperand();
      addStoreEdge(Val, Ptr);
    }

    static bool isFunctionExternal(Function *Fn) {
      //return !Fn->hasExactDefinition();
		return Fn->isDeclaration() || Fn->isInterposable();
    }

    bool tryInterproceduralAnalysis(CallSite CS,
                                    const SmallVectorImpl<Function *> &Fns) {
      
      assert(Fns.size() > 0);

      if (CS.arg_size() > MaxSupportedArgsInSummary)
        return false;

      // Exit early if we'll fail anyway
      for (auto *Fn : Fns) {
        if (isFunctionExternal(Fn)) {
          return false;
		}
        // Fail if the caller does not provide enough arguments
        assert(Fn->arg_size() <= CS.arg_size());
        if (!AA.getSummary(*Fn)) {
	      //errs() << "possible recursive call to " << Fn->getName() << "\n";
          return false;
		}
      }

      for (auto *Fn : Fns) {
        auto Summary = AA.getSummary(*Fn);
        assert(Summary != nullptr);
	    
		if(Fn->isVarArg() && CS.arg_size() > Fn->arg_size() + 1) {
		   //Currently variadic arguments cannot be modelled precisely due to
		   //bitcasting while retrieving var args changeing the maximum pointer level
		   for (auto i = Fn->arg_size(); i != CS.arg_size(); i++) {
			auto Arg = CS.getArgument(i);
			if(Arg->getType()->isPointerTy()) {
			  Graph.addNode(InstantiatedValue{Arg, 1});
			  Graph.addAttr(InstantiatedValue{Arg, 0}, getAttrEscaped());
              Graph.addAttr(InstantiatedValue{Arg, 1}, getAttrUnknown());
			}
		   }
		   //unsigned VAStart = Fn->arg_size();
           //auto i = VAStart;
		   //auto ArgNode = InstantiatedValue{CS.getArgument(i), 0};
		   //Graph.addNode(ArgNode);
		   //for(unsigned j = VAStart + 1; j != CS.arg_size(); i++, j++) {
		   // auto ArgNextNode = InstantiatedValue{CS.getArgument(j), 0};
		   // Graph.addNode(ArgNextNode);
		   // Graph.addEdge(ArgNode, ArgNextNode);
		   // ArgNode = ArgNextNode;
		   //}
		   //Graph.addEdge(ArgNode, InstantiatedValue{CS.getArgument(VAStart), 0});

		}

        auto &RetParamRelations = Summary->RetParamRelations;
        for (auto &Relation : RetParamRelations) {
          auto IRelation = instantiateExternalRelation(Relation, CS, GlobalVars);
          if (IRelation.hasValue()) {
            Graph.addNode(IRelation->From);
            Graph.addNode(IRelation->To);
            Graph.addEdge(IRelation->From, IRelation->To);
          }
        }

        auto &RetParamAttributes = Summary->RetParamAttributes;
        for (auto &Attribute : RetParamAttributes) {
          auto IAttr = instantiateExternalAttribute(Attribute, CS, GlobalVars);
          if (IAttr.hasValue())
            Graph.addNode(IAttr->IValue, IAttr->Attr);
        }
      }

      return true;
    }


    void visitCallSite(CallSite CS) {
      auto Inst = CS.getInstruction();

	// Make sure all arguments and return value are added to the graph first
      for (Value *V : CS.args()) {
        if (V->getType()->isPointerTy()) {
          addNode(V);
		}
	  }
      if (Inst->getType()->isPointerTy())
        addNode(Inst);
	  
      if(IsVarArg &&
		 isa<VAStartInst>(Inst)) {
		VAArgs.push_back(CS.getArgOperand(0));
		return;
      }

	  if(handleKnownFunctions(CS, &TLI, Graph))
		return;

      // TODO: Add support for noalias args/all the other fun function
      // attributes that we can tack on.
      SmallVector<Function *, 4> Targets;
      if (getPossibleTargets(CS, Targets)) {
        if (tryInterproceduralAnalysis(CS, Targets))
          return;
	  }

	  //errs() << "unhandled call instruction  " << *Inst << "\n"; 
      if (auto F = CS.getCalledFunction()) {
        auto FName = F->getName();
		int status;
		auto demangled = abi::__cxa_demangle(FName.begin(), 0, 0, &status);
		if (status==0) {
			//errs() << FName << " demangles to " << demangled << "\n\n";
		}
	  }

      // Because the function is opaque, we need to note that anything
      // could have happened to the arguments (unless the function is marked
      // readonly or readnone), and that the result could alias just about
      // anything, too (unless the result is marked noalias).
      if (!CS.onlyReadsMemory())
        for (Value *V : CS.args()) {
          if (V->getType()->isPointerTy()) {
            // The argument itself escapes.
            Graph.addAttr(InstantiatedValue{V, 0}, getAttrUnknown());
            // The fate of argument memory is unknown. Note that since
            // AliasAttrs is transitive with respect to dereference, we only
            // need to specify it for the first-level memory.
            //Graph.addNode(InstantiatedValue{V, 1}, getAttrUnknown());
          }
        }

      if (Inst->getType()->isPointerTy()) {
		//Return values from unknown functions are unknown
		Graph.addAttr(InstantiatedValue{Inst, 0}, getAttrUnknown());
        //auto *Fn = CS.getCalledFunction();
        //if (Fn == nullptr || !Fn->returnDoesNotAlias())
          // No need to call addNode() since we've added Inst at the
          // beginning of this function and we know it is not a global.
          //Graph.addAttr(InstantiatedValue{Inst, 0}, getAttrUnknown());
      }
    }

    /// Because vectors/aggregates are immutable and unaddressable, there's
    /// nothing we can do to coax a value out of them, other than calling
    /// Extract{Element,Value}. We can effectively treat them as pointers to
    /// arbitrary memory locations we can store in and load from.
    void visitExtractElementInst(ExtractElementInst &Inst) {
      auto *Ptr = Inst.getVectorOperand();
      auto *Val = &Inst;
      addLoadEdge(Ptr, Val);
    }

    void visitInsertElementInst(InsertElementInst &Inst) {
      auto *Vec = Inst.getOperand(0);
      auto *Val = Inst.getOperand(1);
      addAssignEdge(Vec, &Inst);
      addStoreEdge(Val, &Inst);
    }

    void visitLandingPadInst(LandingPadInst &Inst) {
      // Exceptions come from "nowhere", from our analysis' perspective.
      // So we place the instruction its own group, noting that said group may
      // alias externals
      if (Inst.getType()->isPointerTy())
        addNode(&Inst, getAttrUnknown());
    }

    void visitInsertValueInst(InsertValueInst &Inst) {
      auto *Agg = Inst.getOperand(0);
      auto *Val = Inst.getOperand(1);
      addAssignEdge(Agg, &Inst);
      addStoreEdge(Val, &Inst);
    }

    void visitExtractValueInst(ExtractValueInst &Inst) {
      auto *Ptr = Inst.getAggregateOperand();
      addLoadEdge(Ptr, &Inst);
    }

    void visitShuffleVectorInst(ShuffleVectorInst &Inst) {
      auto *From1 = Inst.getOperand(0);
      auto *From2 = Inst.getOperand(1);
      addAssignEdge(From1, &Inst);
      addAssignEdge(From2, &Inst);
    }

    void visitConstantExpr(ConstantExpr *CE) {
      switch (CE->getOpcode()) {
      case Instruction::GetElementPtr: {
        auto GEPOp = cast<GEPOperator>(CE);
        visitGEP(*GEPOp);
        break;
      }

      case Instruction::PtrToInt: {
        addNode(CE->getOperand(0), getAttrEscaped());
        break;
      }

      case Instruction::IntToPtr: {
        addNode(CE, getAttrUnknown());
        break;
      }

      case Instruction::BitCast:
      case Instruction::AddrSpaceCast:
      case Instruction::Trunc:
      case Instruction::ZExt:
      case Instruction::SExt:
      case Instruction::FPExt:
      case Instruction::FPTrunc:
      case Instruction::UIToFP:
      case Instruction::SIToFP:
      case Instruction::FPToUI:
      case Instruction::FPToSI: {
        addAssignEdge(CE->getOperand(0), CE);
        break;
      }

      case Instruction::Select: {
        addAssignEdge(CE->getOperand(1), CE);
        addAssignEdge(CE->getOperand(2), CE);
        break;
      }

      case Instruction::InsertElement:
      case Instruction::InsertValue: {
        addAssignEdge(CE->getOperand(0), CE);
        addStoreEdge(CE->getOperand(1), CE);
        break;
      }

      case Instruction::ExtractElement:
      case Instruction::ExtractValue: {
        addLoadEdge(CE->getOperand(0), CE);
        break;
      }

      case Instruction::Add:
      case Instruction::Sub:
      case Instruction::FSub:
      case Instruction::Mul:
      case Instruction::FMul:
      case Instruction::UDiv:
      case Instruction::SDiv:
      case Instruction::FDiv:
      case Instruction::URem:
      case Instruction::SRem:
      case Instruction::FRem:
      case Instruction::And:
      case Instruction::Or:
      case Instruction::Xor:
      case Instruction::Shl:
      case Instruction::LShr:
      case Instruction::AShr:
      case Instruction::ICmp:
      case Instruction::FCmp:
      case Instruction::ShuffleVector: {
        addAssignEdge(CE->getOperand(0), CE);
        addAssignEdge(CE->getOperand(1), CE);
        break;
      }

      default:
        llvm_unreachable("Unknown instruction type encountered!");
      }
    }
  };

  // Helper functions

  // Determines whether or not we an instruction is useless to us (e.g.
  // FenceInst)
  static bool hasUsefulEdges(Instruction *Inst) {
    bool IsNonInvokeRetTerminator = Inst->isTerminator() &&
                                    !isa<InvokeInst>(Inst) &&
                                    !isa<ReturnInst>(Inst);
    return !isa<CmpInst>(Inst) && !isa<FenceInst>(Inst) &&
           !IsNonInvokeRetTerminator;
  }

  void addArgumentToGraph(Argument &Arg) {
    if (Arg.getType()->isPointerTy()) {
      Graph.addNode(InstantiatedValue{&Arg, 0},
                    getGlobalOrArgAttrFromValue(Arg));
      // Pointees of a formal parameter is known to the caller
      Graph.addNode(InstantiatedValue{&Arg, 1}, getAttrCaller());
    }
  }

  // Given an Instruction, this will add it to the graph, along with any
  // Instructions that are potentially only available from said Instruction
  // For example, given the following line:
  //   %0 = load i16* getelementptr ([1 x i16]* @a, 0, 0), align 2
  // addInstructionToGraph would add both the `load` and `getelementptr`
  // instructions to the graph appropriately.
  void addInstructionToGraph(GetEdgesVisitor &Visitor, Instruction &Inst) {
    if (!hasUsefulEdges(&Inst))
      return;

    Visitor.visit(Inst);
  }

  // Builds the graph needed for constructing the StratifiedSets for the given
  // function
  void buildGraphFrom(Function &Fn) {
    GetEdgesVisitor Visitor(*this, Fn.getParent()->getDataLayout());


    for (auto &Bb : Fn.getBasicBlockList())
      for (auto &Inst : Bb.getInstList())
        addInstructionToGraph(Visitor, Inst);

    for (auto &Arg : Fn.args())
      addArgumentToGraph(Arg);
  }

public:
  CFLGraphBuilder(CFLAA &Analysis, const TargetLibraryInfo &TLI, SmallVector<Value *, 4> &GlobalVars, Function &Fn)
      : Analysis(Analysis), TLI(TLI), GlobalVars(GlobalVars), IsVarArg(Fn.isVarArg()), Graph(TLI) {
    buildGraphFrom(Fn);
  }

  CFLGraph &getCFLGraph() { return Graph; }
  const SmallVector<Value *, 4> &getReturnValues() const {
    return ReturnedValues;
  }

  const SmallVector<Value *, 4> &getVAArgs() const {
    return VAArgs;
  }

};

} // end namespace cflta
} // end namespace llvm

#endif //LLVM_LIB_ANALYSIS_CFLGRAPH_BUILDER_H
