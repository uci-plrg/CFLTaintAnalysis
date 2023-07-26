#ifndef LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_CONFIG_H
#define LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_CONFIG_H

#include <stdlib.h>

static const std::string PMAllocators[] = {
	//libpmem
    "pmem_map_file",
	//pmdk/common
	"util_map_sync"
}; 


static const std::string PMAllocatorsArg7Lv1[] =  {
	//libpmem2
	"file_map",
};

static const std::string noAliasFunctions[] = {
	"rand",
	"__cxa_begin_catch", 
	//std functions
	"_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc", //std::basic_ostream<char, std::char_traits<char> >& std::operator<< <std::char_traits<char> >(std::basic_ostream<char, std::char_traits<char> >&, char const*)
	"_ZNSolsEPFRSoS_E", //std::ostream::operator<<(std::ostream& (*)(std::ostream&)),
	"_ZStanSt12memory_orderSt23__memory_order_modifier", //std::operator&(std::memory_order, std::__memory_order_modifier)
	"_ZNSt6chrono3_V212system_clock3nowEv", //std::chrono::_V2::system_clock::now()
	"_ZNSt6thread2idC2Ev", //std::thread::id::id()
	"_ZNSt6thread6_StateC2Ev", //std::thread::_State::_State()
	"_ZNSt6threadD2Ev", //std::thread::~thread()
	"_ZSt9terminatev", //std::terminate()
	"_ZNSt6thread15_M_start_threadESt10unique_ptrINS_6_StateESt14default_deleteIS1_EEPFvvE", //std::thread::_M_start_thread(std::unique_ptr<std::thread::_State, std::default_delete<std::thread::_State> >, void (*)())
	"_ZSt20__throw_length_errorPKc", //std::__throw_length_error(char const*)
	"_ZSt17__throw_bad_allocv", //std::__throw_bad_alloc()
	"_ZNSt6thread4joinEv", //std::thread::join()
	"__assert_fail",
	//posix functions
	"open",
	"fsync",
	"stat",
	"unlink",
	"access",
	"fopen",
	"fdopen",
	"chmod",
	"mkstemp",
	"posix_fallocate",
	"ftruncate",
	"flock",
	"writev",
	"clock_gettime",
	"rand_r",
	"unsetenv",
	"setenv",
	"secure_getenv",
	"strsignal",
	"execv",
};
#endif //LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_CONFIG_H
