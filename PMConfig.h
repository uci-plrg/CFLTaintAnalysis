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

static const std::string PMStructTypes[] = {
	//"struct.PMEMobjpool",
	//"struct.ulog",
	"", 
};
#endif //LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_CONFIG_H
