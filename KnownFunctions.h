//// this file contains models of c and c++ library functions
//// modified from https://github.com/grievejia/andersen/blob/master/lib/ExternalLibrary.cpp

#ifndef LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_H
#define LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_H

#include "CFLGraph.h"
#include "CFLTaintAnalysisUtils.h"
#include "KnownFunctionsConfig.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"

#include <algorithm>

#define ALL_ALLOC_FN_PMEM 1

using namespace llvm;
using namespace llvm::cflta;


//intrinsics that have no effect on aliasing
bool isNoAliasIntrinsic(const IntrinsicInst *II) {
    if(isa<ConstrainedFPIntrinsic>(II) || 
       isa<AnyMemSetInst>(II) ||
       isa<VAStartInst>(II) ||
       isa<VAEndInst>(II) ||
       isa<InstrProfIncrementInst>(II) ||
       isa<InstrProfValueProfileInst>(II))
	  return true;

	switch (II->getIntrinsicID()) {
      default: break;
      //assume like intrinsics
      case Intrinsic::assume:
      case Intrinsic::sideeffect:
      case Intrinsic::dbg_declare:
      case Intrinsic::dbg_value:
      case Intrinsic::dbg_label:
      case Intrinsic::invariant_start:
      case Intrinsic::invariant_end:
      case Intrinsic::lifetime_start:
      case Intrinsic::lifetime_end:
      case Intrinsic::objectsize:
      case Intrinsic::ptr_annotation:
      case Intrinsic::var_annotation:
      //BinaryOpIntrinsics
      case Intrinsic::uadd_with_overflow:
      case Intrinsic::sadd_with_overflow:
      case Intrinsic::usub_with_overflow:
      case Intrinsic::ssub_with_overflow:
      case Intrinsic::umul_with_overflow:
      case Intrinsic::smul_with_overflow:
      case Intrinsic::uadd_sat:
      case Intrinsic::sadd_sat:
      case Intrinsic::usub_sat:
      case Intrinsic::ssub_sat:
	  //unclassified
	  case Intrinsic::bswap:
	  case Intrinsic::ctlz:
        return true;
    }

  return false;
}

bool handleKnownFunctions(const CallSite CS, const TargetLibraryInfo *TLI, CFLGraph &Graph) {
  auto I = CS.getInstruction();
  auto IV = InstantiatedValue{cast<CallBase>(I),  0};

  if(auto II = dyn_cast<IntrinsicInst>(I)) {
	if(isNoAliasIntrinsic(II))
	  return true;
    else if(auto MT = dyn_cast<AnyMemTransferInst>(II)) {
		Graph.addEdge(InstantiatedValue{MT->getSource(), 0}, InstantiatedValue{MT->getDest(), 0});
        return true;   
    }
    else if(auto VI = dyn_cast<VACopyInst>(II)) {
		Graph.addEdge(InstantiatedValue{VI->getSrc(), 0}, InstantiatedValue{VI->getDest(), 0});
        return true;   
    }
    else if(auto VI = dyn_cast<VAArgInst>(II)) {
		auto VAArgList = VI->getPointerOperand();
		Graph.addNode(InstantiatedValue{VAArgList, 1});
		Graph.addEdge(InstantiatedValue{VAArgList, 1}, InstantiatedValue{VI, 0});
        return true;   
    }

  }
	
  if (isAllocationFn(I, TLI)) {
#ifdef ALL_ALLOC_FN_PMEM
	Graph.addAttr(IV, getAttrTainted());
#endif
	return true;
  }

  if (isFreeCall(I, TLI))
    return true;

  const Function *Callee = CS.getCalledFunction();
  if (Callee == nullptr)
    return false;

  std::string FnName = Callee->getName().str();

  if(is_contained(PMAllocators, FnName)) {
	Graph.addAttr(IV, getAttrTainted());
	return true;
  }
  if(is_contained(PMAllocatorsArg7Lv1, FnName)) {
	auto Arg = CS.getArgOperand(7);
	Graph.addNode(InstantiatedValue{Arg, 1}, getAttrTainted());
    return true;
  }
  if(is_contained(noAliasFunctions, FnName))
	return true;
	
  //TODO: Should non-built-in calls be treated differently?
  if(auto CB = dyn_cast<CallBase>(CS.getInstruction())) {
	if(CB->isNoBuiltin())
	  return false;
  }

  LibFunc TLIFn;
  if (!TLI || !TLI->getLibFunc(FnName, TLIFn) || !TLI->has(TLIFn))
    return false;

  switch(TLIFn) {
	case LibFunc_under_IO_getc:
	case LibFunc_under_IO_putc:
	case LibFunc_acos_finite:
	case LibFunc_acosf_finite:
	case LibFunc_acosh_finite:
	case LibFunc_acoshf_finite:
	case LibFunc_acoshl_finite:
	case LibFunc_acosl_finite:
	case LibFunc_asin_finite:
	case LibFunc_asinf_finite:
	case LibFunc_asinl_finite:
	case LibFunc_atan2_finite:
	case LibFunc_atan2f_finite:
	case LibFunc_atan2l_finite:
	case LibFunc_atanh_finite:
	case LibFunc_atanhf_finite:
	case LibFunc_atanhl_finite:
	case LibFunc_cosh_finite:
	case LibFunc_coshf_finite:
	case LibFunc_coshl_finite:
	case LibFunc_cospi:
	case LibFunc_cospif:
	case LibFunc_cxa_atexit:
	case LibFunc_cxa_guard_abort:
	case LibFunc_cxa_guard_acquire:
	case LibFunc_cxa_guard_release:
	case LibFunc_exp10_finite:
	case LibFunc_exp10f_finite:
	case LibFunc_exp10l_finite:
	case LibFunc_exp2_finite:
	case LibFunc_exp2f_finite:
	case LibFunc_exp2l_finite:
	case LibFunc_exp_finite:
	case LibFunc_expf_finite:
	case LibFunc_expl_finite:
	case LibFunc_dunder_isoc99_scanf:
	case LibFunc_dunder_isoc99_sscanf:
	case LibFunc_log10_finite:
	case LibFunc_log10f_finite:
	case LibFunc_log10l_finite:
	case LibFunc_log2_finite:
	case LibFunc_log2f_finite:
	case LibFunc_log2l_finite:
	case LibFunc_log_finite:
	case LibFunc_logf_finite:
	case LibFunc_logl_finite:
	case LibFunc_memset_chk:
	case LibFunc_pow_finite:
	case LibFunc_powf_finite:
	case LibFunc_powl_finite:
	case LibFunc_sincospi_stret:
	case LibFunc_sincospif_stret:
	case LibFunc_sinh_finite:
	case LibFunc_sinhf_finite:
	case LibFunc_sinhl_finite:
	case LibFunc_sinpi:
	case LibFunc_sinpif:
	case LibFunc_sqrt_finite:
	case LibFunc_sqrtf_finite:
	case LibFunc_sqrtl_finite:
	case LibFunc_dunder_strdup:
	case LibFunc_dunder_strndup:
	case LibFunc_abs:
	case LibFunc_access:
	case LibFunc_acos:
	case LibFunc_acosf:
	case LibFunc_acosh:
	case LibFunc_acoshf:
	case LibFunc_acoshl:
	case LibFunc_acosl:
	case LibFunc_asin:
	case LibFunc_asinf:
	case LibFunc_asinh:
	case LibFunc_asinhf:
	case LibFunc_asinhl:
	case LibFunc_asinl:
	case LibFunc_atan:
	case LibFunc_atan2:
	case LibFunc_atan2f:
	case LibFunc_atan2l:
	case LibFunc_atanf:
	case LibFunc_atanh:
	case LibFunc_atanhf:
	case LibFunc_atanhl:
	case LibFunc_atanl:
	case LibFunc_atof:
	case LibFunc_atoi:
	case LibFunc_atol:
	case LibFunc_atoll:
	case LibFunc_bcmp:
	case LibFunc_bcopy:
	case LibFunc_bzero:
	case LibFunc_cabs:
	case LibFunc_cabsf:
	case LibFunc_cabsl:
	case LibFunc_calloc:
	case LibFunc_cbrt:
	case LibFunc_cbrtf:
	case LibFunc_cbrtl:
	case LibFunc_ceil:
	case LibFunc_ceilf:
	case LibFunc_ceill:
	case LibFunc_chmod:
	case LibFunc_chown:
	case LibFunc_clearerr:
	case LibFunc_closedir:
	case LibFunc_copysign:
	case LibFunc_copysignf:
	case LibFunc_copysignl:
	case LibFunc_cos:
	case LibFunc_cosf:
	case LibFunc_cosh:
	case LibFunc_coshf:
	case LibFunc_coshl:
	case LibFunc_cosl:
	case LibFunc_ctermid:
	case LibFunc_execl:
	case LibFunc_execle:
	case LibFunc_execlp:
	case LibFunc_execv:
	case LibFunc_execvP:
	case LibFunc_execve:
	case LibFunc_execvp:
	case LibFunc_execvpe:
	case LibFunc_exp:
	case LibFunc_exp10:
	case LibFunc_exp10f:
	case LibFunc_exp10l:
	case LibFunc_exp2:
	case LibFunc_exp2f:
	case LibFunc_exp2l:
	case LibFunc_expf:
	case LibFunc_expl:
	case LibFunc_expm1:
	case LibFunc_expm1f:
	case LibFunc_expm1l:
	case LibFunc_fabs:
	case LibFunc_fabsf:
	case LibFunc_fabsl:
	case LibFunc_fclose:
	case LibFunc_fdopen:
	case LibFunc_feof:
	case LibFunc_ferror:
	case LibFunc_fflush:
	case LibFunc_ffs:
	case LibFunc_ffsl:
	case LibFunc_ffsll:
	case LibFunc_fgetc:
	case LibFunc_fgetc_unlocked:
	case LibFunc_fgetpos:
	case LibFunc_fileno:
	case LibFunc_fiprintf:
	case LibFunc_flockfile:
	case LibFunc_floor:
	case LibFunc_floorf:
	case LibFunc_floorl:
	case LibFunc_fls:
	case LibFunc_flsl:
	case LibFunc_flsll:
	case LibFunc_fmax:
	case LibFunc_fmaxf:
	case LibFunc_fmaxl:
	case LibFunc_fmin:
	case LibFunc_fminf:
	case LibFunc_fminl:
	case LibFunc_fmod:
	case LibFunc_fmodf:
	case LibFunc_fmodl:
	case LibFunc_fopen:
	case LibFunc_fopen64:
	case LibFunc_fork:
	case LibFunc_fprintf:
	case LibFunc_fputc:
	case LibFunc_fputc_unlocked:
	case LibFunc_fputs:
	case LibFunc_fputs_unlocked:
	case LibFunc_fread:
	case LibFunc_fread_unlocked:
	case LibFunc_frexp:
	case LibFunc_frexpf:
	case LibFunc_frexpl:
	case LibFunc_fscanf:
	case LibFunc_fseek:
	case LibFunc_fseeko:
	case LibFunc_fseeko64:
	case LibFunc_fsetpos:
	case LibFunc_fstat:
	case LibFunc_fstat64:
	case LibFunc_fstatvfs:
	case LibFunc_fstatvfs64:
	case LibFunc_ftell:
	case LibFunc_ftello:
	case LibFunc_ftello64:
	case LibFunc_ftrylockfile:
	case LibFunc_funlockfile:
	case LibFunc_fwrite:
	case LibFunc_fwrite_unlocked:
	case LibFunc_getc:
	case LibFunc_getc_unlocked:
	case LibFunc_getchar:
	case LibFunc_getchar_unlocked:
	case LibFunc_getenv:
	case LibFunc_getitimer:
	case LibFunc_getlogin_r:
	case LibFunc_getpwnam:
	case LibFunc_gettimeofday:
	case LibFunc_htonl:
	case LibFunc_htons:
	case LibFunc_iprintf:
	case LibFunc_isascii:
	case LibFunc_isdigit:
	case LibFunc_labs:
	case LibFunc_lchown:
	case LibFunc_ldexp:
	case LibFunc_ldexpf:
	case LibFunc_ldexpl:
	case LibFunc_llabs:
	case LibFunc_log:
	case LibFunc_log10:
	case LibFunc_log10f:
	case LibFunc_log10l:
	case LibFunc_log1p:
	case LibFunc_log1pf:
	case LibFunc_log1pl:
	case LibFunc_log2:
	case LibFunc_log2f:
	case LibFunc_log2l:
	case LibFunc_logb:
	case LibFunc_logbf:
	case LibFunc_logbl:
	case LibFunc_logf:
	case LibFunc_logl:
	case LibFunc_lstat:
	case LibFunc_lstat64:
	case LibFunc_malloc:
	case LibFunc_memalign:
	case LibFunc_memcmp:
	case LibFunc_memset:
	case LibFunc_memset_pattern16:
	case LibFunc_mkdir:
	case LibFunc_mktime:
	case LibFunc_modf:
	case LibFunc_modff:
	case LibFunc_modfl:
	case LibFunc_nearbyint:
	case LibFunc_nearbyintf:
	case LibFunc_nearbyintl:
	case LibFunc_ntohl:
	case LibFunc_ntohs:
	case LibFunc_open:
	case LibFunc_open64:
	case LibFunc_opendir:
	case LibFunc_pclose:
	case LibFunc_perror:
	case LibFunc_popen:
	case LibFunc_posix_memalign:
	case LibFunc_pow:
	case LibFunc_powf:
	case LibFunc_powl:
	case LibFunc_pread:
	case LibFunc_printf:
	case LibFunc_putc:
	case LibFunc_putc_unlocked:
	case LibFunc_putchar:
	case LibFunc_putchar_unlocked:
	case LibFunc_puts:
	case LibFunc_pwrite:
	case LibFunc_qsort:
	case LibFunc_read:
	case LibFunc_readlink:
	case LibFunc_realpath:
	case LibFunc_remove:
	case LibFunc_rename:
	case LibFunc_rewind:
	case LibFunc_rint:
	case LibFunc_rintf:
	case LibFunc_rintl:
	case LibFunc_rmdir:
	case LibFunc_round:
	case LibFunc_roundf:
	case LibFunc_roundl:
	case LibFunc_scanf:
	case LibFunc_setbuf:
	case LibFunc_setitimer:
	case LibFunc_setvbuf:
	case LibFunc_sin:
	case LibFunc_sinf:
	case LibFunc_sinh:
	case LibFunc_sinhf:
	case LibFunc_sinhl:
	case LibFunc_sinl:
	case LibFunc_siprintf:
	case LibFunc_snprintf:
	case LibFunc_sprintf:
	case LibFunc_sqrt:
	case LibFunc_sqrtf:
	case LibFunc_sqrtl:
	case LibFunc_sscanf:
	case LibFunc_stat:
	case LibFunc_stat64:
	case LibFunc_statvfs:
	case LibFunc_statvfs64:
	case LibFunc_strcasecmp:
	case LibFunc_strcmp:
	case LibFunc_strcoll:
	case LibFunc_strcspn:
	case LibFunc_strlen:
	case LibFunc_strncasecmp:
	case LibFunc_strncmp:
	case LibFunc_strnlen:
	case LibFunc_strspn:
	case LibFunc_strxfrm:
	case LibFunc_system:
	case LibFunc_tan:
	case LibFunc_tanf:
	case LibFunc_tanh:
	case LibFunc_tanhf:
	case LibFunc_tanhl:
	case LibFunc_tanl:
	case LibFunc_times:
	case LibFunc_tmpfile:
	case LibFunc_tmpfile64:
	case LibFunc_toascii:
	case LibFunc_trunc:
	case LibFunc_truncf:
	case LibFunc_truncl:
	case LibFunc_uname:
	case LibFunc_ungetc:
	case LibFunc_unlink:
	case LibFunc_unsetenv:
	case LibFunc_utime:
	case LibFunc_utimes:
	case LibFunc_vfprintf:
	case LibFunc_vfscanf:
	case LibFunc_vprintf:
	case LibFunc_vscanf:
	case LibFunc_vsnprintf:
	case LibFunc_vsprintf:
	case LibFunc_vsscanf:
	case LibFunc_wcslen:
	case LibFunc_write:
		return true;
	//return value aliases with first arg
    case LibFunc_strstr:
	case LibFunc_strrchr:
	case LibFunc_strpbrk:
	case LibFunc_strncpy:
	case LibFunc_strncat:
	case LibFunc_strcpy:
	case LibFunc_strchr:
	case LibFunc_strcat:
	case LibFunc_memrchr:
	case LibFunc_memchr:
	case LibFunc_strcpy_chk:
	case LibFunc_strncpy_chk:
	case LibFunc_fgets:
	case LibFunc_gets:
	case LibFunc_fgets_unlocked:
	case LibFunc_stpcpy:
	case LibFunc_stpncpy:
	case LibFunc_stpcpy_chk:
	case LibFunc_stpncpy_chk: {
		auto arg0 = CS.getArgument(0);
        Graph.addEdge(InstantiatedValue{arg0, 0}, InstantiatedValue{I, 0});
		return true;
    }
	//unknown if the arg is NULL, else return value aliases with first arg
	case LibFunc_strtok_r:
	case LibFunc_strtok:
	case LibFunc_dunder_strtok_r: {
		auto arg0 = CS.getArgument(0);
		if(isa<ConstantPointerNull>(arg0))
			return false;
		Graph.addEdge(InstantiatedValue{arg0, 0}, InstantiatedValue{I, 0});
		return true;
	}
    //pointee of return value aliases with first arg
    case LibFunc_memcpy_chk:
    case LibFunc_memmove_chk:
    case LibFunc_memccpy:
    case LibFunc_memcpy:
    case LibFunc_memmove:
    case LibFunc_mempcpy: {
		if(maxDerefLevel(I) > 1) {
			auto arg0 = CS.getArgument(0);
			Graph.addNode(InstantiatedValue{arg0, 1});
			Graph.addNode(InstantiatedValue{I, 1});
			Graph.addEdge(InstantiatedValue{arg0, 1}, InstantiatedValue{I, 1});
        }
		return true;
	}
	//allocate new node if arg is NULL, else pointee of return value alises with pointee of first arg
	case LibFunc_realloc:
	case LibFunc_reallocf: {
		auto arg0 = CS.getArgument(0);
		if(!isa<ConstantPointerNull>(arg0) && maxDerefLevel(I) > 1) { 
			Graph.addNode(InstantiatedValue{arg0, 1});
			Graph.addNode(InstantiatedValue{I, 1});
			Graph.addEdge(InstantiatedValue{arg0, 1}, InstantiatedValue{I, 1});
		}
		return true;
	}
	//conversion functions
	case LibFunc_strtod:
	case LibFunc_strtof:
	case LibFunc_strtol:
	case LibFunc_strtold:
	case LibFunc_strtoll:
	case LibFunc_strtoul:
	case LibFunc_strtoull: {
		auto arg0 = CS.getArgument(0);
		auto arg1 = CS.getArgument(1);
		if (!isa<ConstantPointerNull>(arg1) && 
			maxDerefLevel(arg1) > 1) {
			Graph.addNode(InstantiatedValue{arg1, 1});
			Graph.addEdge(InstantiatedValue{arg0, 0}, InstantiatedValue{arg1, 1});
		}
		return true;
	}
    default: 
	  return false;
  }
}

#endif //LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_H

