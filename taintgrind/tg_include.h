#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_options.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_machine.h"     // VG_(fnptr_to_fnentry)
#include "pub_tool_aspacemgr.h"   
#include "pub_tool_threadstate.h"   
#include "vki/vki-scnums-x86-linux.h"

IRExpr *tg_deepCopyIRExpr(IRExpr *expr);
