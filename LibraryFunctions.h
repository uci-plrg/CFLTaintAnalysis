//// this file contains models of c and c++ library functions
//// modified from https://github.com/grievejia/andersen/blob/master/lib/ExternalLibrary.cpp

#ifndef LLVM_LIB_ANALYSIS_TAINT_LIBRARY_FUNCTION_H
#define LLVM_LIB_ANALYSIS_TAINT_LIBRARY_FUNCTION_H

#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"

#include <algorithm>

using namespace llvm;


static const Function *getCalledFunction(const Value *V, bool LookThroughBitCast,
                                         bool &IsNoBuiltin) {
  // Don't care about intrinsics in this case.
  if (isa<IntrinsicInst>(V))
    return nullptr;

  if (LookThroughBitCast)
    V = V->stripPointerCasts();

  ImmutableCallSite CS(V);
  if (!CS.getInstruction())
    return nullptr;

  IsNoBuiltin = CS.isNoBuiltin();

  if (const Function *Callee = CS.getCalledFunction())
    return Callee;
  return nullptr;
}

//assume like intrinsics are annotations and have no effect on aliasing
static bool isAssumeLikeIntrinsic(const Instruction *I) {
  if (const CallInst *CI = dyn_cast<CallInst>(I))
    if (Function *F = CI->getCalledFunction())
      switch (F->getIntrinsicID()) {
      default: break;
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
        return true;
      }

  return false;
}

bool handleLibraryFunction(const Instruction *I, const TargetLibraryInfo *TLI) {

  if(isAssumeLikeIntrinsic(I))
	return true;

  bool IsNoBuiltinCall;
  const Function *Callee =
      getCalledFunction(I, /*LookThroughBitCast=*/false, IsNoBuiltinCall);
  if (Callee == nullptr || IsNoBuiltinCall)
    return false;

  StringRef FnName = Callee->getName();
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
	//TODO: handle special cases
    default: 
	  return false;
  }
}

#endif
