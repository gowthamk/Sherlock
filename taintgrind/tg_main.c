
/*--------------------------------------------------------------------*/
/*--- Taintgrind: The Taint Analysis Valgrind tool.               tg_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Tainshrind, the Taint Analysis Valgrind tool,
   which traces the propagation of tainted inputs in the program.

   Copyright (C) 2002-2011 Gowtham
      gowtham@purdue.edu

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#include "tg_include.h"

static Bool clo_trace_mem    = False;


/*------------------------------------------------------------*/
/*--- Stuff for --trace-mem                                ---*/
/*------------------------------------------------------------*/

#define MAX_DSIZE    512
#define N_PRIMARY_MAP 65536

typedef
   IRExpr 
   IRAtom;

typedef
    struct {
        UChar abits[65536];
    } SecMap;

/* Up to this many unnotified events are allowed.  Must be at least two,
   so that reads and writes to the same address can be merged into a modify.
   Beyond that, larger numbers just potentially induce more spilling due to
   extending live ranges of address temporaries. */

static Char       global_fnname[100];
static SecMap* primary_map[N_PRIMARY_MAP];
static SecMap default_map;
static Bool temp_shadow[N_PRIMARY_MAP];
static int put_count = 0;

/* SHADOW MEM FUNCTIONS  */
static void init_shadow_memory ( void )
{
    int i=0;
    for (i = 0; i < 65536; i++)
        default_map.abits[i] = 0;
    for (i = 0; i < 65536; i++)
        primary_map[i] = &default_map;
    for (i = 0; i < 65536; i++)
        temp_shadow[i] = 0;
}
static SecMap* alloc_secondary_map (void)
{
    int i=0;
    SecMap *map =VG_(am_shadow_alloc)(sizeof(SecMap));
    for (i = 0; i < 65536; i++)
        map->abits[i] = 0;
    return map;
}
static Bool is_accessible(UWord addr)
{
    return (primary_map[addr>>16] != &default_map);
}
static void taint_addr(UWord addr)
{
    if (primary_map[(addr) >> 16] == &default_map)
        primary_map[(addr) >> 16] = alloc_secondary_map();
    SecMap *map = primary_map[addr>>16];
    map->abits[addr&0xFFFF] = 1;
    return;
}
static void untaint_addr(UWord addr)
{
    SecMap *map = primary_map[addr>>16];
    map->abits[addr&0xFFFF] = 0;
    return;
}
static void taint_temp(IRTemp tmp)
{
    //VG_(printf)("Temp %d has been tainted\n",tmp);
    tl_assert(tmp<N_PRIMARY_MAP);
    temp_shadow[tmp] = 1;
}
static void untaint_temp(IRTemp tmp)
{
    //VG_(printf)("Temp %d has been untainted\n",tmp);
    tl_assert(tmp<N_PRIMARY_MAP);
    temp_shadow[tmp] = 0;
}
static Bool is_addr_tainted(UWord addr)
{
    return (is_accessible(addr) && (primary_map[addr>>16]->abits[addr&0xFFFF]==1));
}
static Bool is_temp_tainted(IRTemp tmp)
{
    return temp_shadow[tmp];
}
static void pre_read(ThreadId tid, UInt syscallno,
                                    UWord* args, UInt nArgs)
{
}
static void post_read(ThreadId tid, UInt syscallno,
                                    UWord* args, UInt nArgs, SysRes res)
{
    if(clo_trace_mem && syscallno == __NR_read && args[0] == 0){
        Int size = args[2];
        Int i;
        UWord addr = args[1];
        for(i=0;i<size;i++){
            taint_addr(addr+i);
            //VG_(printf)("0x%x 0x%x DD\n",addr+i,*(UChar *)(addr+i));
        }
        //VG_(printf)("%d\n",*(int *)(addr+3));
        VG_(printf)("Syscall no: %d with arg[0] %08lx and arg[1] %08lx and arg[2] %d\n",syscallno,args[0],args[1],size);
    }

}
static Bool is_irexpr_tainted(IRExpr *expr)
{
    UChar reg_shadow;
    Int offset;
    ThreadId tid = VG_(get_running_tid)();
    IRTemp tmp;
    switch(expr->tag)
    {
        case Iex_Get:
           offset = expr->Iex.Get.offset;
           VG_(get_shadow_regs_area) ( tid, 
                            /*DST UChar* */&reg_shadow,/*Shadow No*/1,
                            /*PtrdiffT*/ offset, /*SizeT*/1); 
           VG_(printf)("GET Inst. Regshadow(%d) is %d\n",offset,reg_shadow);
           return reg_shadow;
        break;

        case Iex_GetI:
            VG_(printf)("GETI occurance. Not being tracked\n");
        break;

        case Iex_RdTmp:
            tmp = expr->Iex.RdTmp.tmp;
            if(is_temp_tainted(tmp)){
                //VG_(printf)("Tainted read from temp %d\n",tmp);
            }
            return is_temp_tainted(tmp);
        break;

        case Iex_Qop:
            return (is_irexpr_tainted(expr->Iex.Qop.arg1) ||
                    is_irexpr_tainted(expr->Iex.Qop.arg2) || 
                    is_irexpr_tainted(expr->Iex.Qop.arg3) ||
                    is_irexpr_tainted(expr->Iex.Qop.arg4));
        break;

        case Iex_Triop:
            return (is_irexpr_tainted(expr->Iex.Triop.arg1) ||
                    is_irexpr_tainted(expr->Iex.Triop.arg2) || 
                    is_irexpr_tainted(expr->Iex.Triop.arg3));
        break;

        case Iex_Binop:
            return (is_irexpr_tainted(expr->Iex.Binop.arg1) ||
                    is_irexpr_tainted(expr->Iex.Binop.arg2));
        break;

        case Iex_Unop:
            return (is_irexpr_tainted(expr->Iex.Unop.arg));
        break;

        case Iex_Load:
            /* Destination of load is tainted in 2 cases:
               1. If the operands used to calculate memory address
                  are tainted, or
               2. If the source memory address is tainted 
               Case 2 is already handled at caller*/
            tl_assert(isIRAtom(expr->Iex.Load.addr));
            return is_irexpr_tainted(expr->Iex.Load.addr);
        break;

        case Iex_Const:
            return False;
        break;

        case Iex_Mux0X:
        case Iex_CCall:
        case Iex_Binder:
            //VG_(printf)("IRExpr tag is 0x%x. Not being handled\n",expr->tag);
        break;

        default :
            VG_(tool_panic)("is_irexpr_tainted");
        break;

    }
    return False;
}
static IRExpr* widenUto32(IRSB* sb, IRExpr* e)
{
   switch (typeOfIRExpr(sb->tyenv,e)) {
      case Ity_I32: return e;
      case Ity_I16: return IRExpr_Unop(Iop_16Uto32,e);
      case Ity_I8:  return IRExpr_Unop(Iop_8Uto32,e);
      default:
          VG_(message)(Vg_FailMsg,"Data Incompatibility. \ 
              See http://sourceforge.net/mailarchive/message.php?msg_id=12963267");
          return NULL;
   }
}
/*------------------------------------------------------------*/
/*---       RUN TIME INSTUMENTATION FUNCTIONS              ---*/
/*------------------------------------------------------------*/
static VG_REGPARM(3) void taint_runtime_put(Int offset, IRExpr *data, Int cnt)
{
    UChar reg_shadow = 1;
    ThreadId tid = VG_(get_running_tid)();
    //VG_(printf)("Inside put helper: Data address(%d) is 0x%x\n",cnt,data);
    tl_assert(isIRAtom(data));
    if(data->tag == Iex_RdTmp)
        VG_(printf)("Register write: %d <- (t%d)\n",offset,data->Iex.RdTmp.tmp);
    if(is_irexpr_tainted(data)){
        VG_(set_shadow_regs_area) ( tid, 
                        /*Shadow No*/1,/*PtrdiffT*/ offset, 
                        /*SizeT*/1,/*src*/&reg_shadow); 
        VG_(printf)("Set shadow for register:%d\n",offset);
    }
    else {
        reg_shadow = 0;
        VG_(set_shadow_regs_area) ( tid, 
                        /*Shadow No*/1,/*PtrdiffT*/ offset, 
                        /*SizeT*/1,/*src*/&reg_shadow); 
        VG_(printf)("Unset shadow for register:%d\n",offset);
    }
    return;
}
static VG_REGPARM(3) void taint_runtime_wrtmp(IRTemp tmp, IRExpr *data, Addr addr)
{
    Bool isTainted = ((data->tag == Iex_Load && is_addr_tainted(addr)) ||
                       is_irexpr_tainted(data));
    if(data->tag==Iex_Load){
        VG_(printf)("Load from address 0x%x to temp %d. isTainted:%d\n",addr,tmp,isTainted);
    }
    else {
        VG_(printf)("Temp %d is being written. RHS is %d and isTainted: %d\n",tmp,data->tag,isTainted);
    }
    if(isTainted)
        taint_temp(tmp);
    else if(is_temp_tainted(tmp))
        untaint_temp(tmp);

    return;
}
static VG_REGPARM(3) void taint_runtime_store(Addr addr, HWord data, IRExpr *addrexpr, IRExpr *dataexpr)
{
    tl_assert(isIRAtom(addrexpr));
    tl_assert(isIRAtom(dataexpr));
    if(dataexpr->tag == Iex_RdTmp)
        VG_(printf)("Writes: 0x%x <- 0x%x(t%d)\n",addr,data,dataexpr->Iex.RdTmp.tmp);
    else if(dataexpr->tag == Iex_Const)
        VG_(printf)("Writes: 0x%x <- 0x%x(const)\n",addr,data);
    if(is_irexpr_tainted(addrexpr) || is_irexpr_tainted(dataexpr)){
        if(dataexpr->tag == Iex_RdTmp){
            //VG_(printf)("Tainted store to 0x%x from temp %d\n",addr,dataexpr->Iex.RdTmp.tmp);
        }
        taint_addr(addr);
        VG_(printf)("0x%x 0x%x DD\n",addr,data);
    }
    else if(is_addr_tainted(addr)){
        untaint_addr(addr);
    }
    return;
}
static VG_REGPARM(3) void taint_runtime_store_special(Addr addr, IRExpr *addrexpr, IRExpr *dataexpr)
{
    tl_assert(isIRAtom(addrexpr));
    tl_assert(isIRAtom(dataexpr));
    if(is_irexpr_tainted(addrexpr) || is_irexpr_tainted(dataexpr)){
        if(dataexpr->tag == Iex_RdTmp){
            VG_(printf)("Tainted store to 0x%x from temp %d\n",addr,dataexpr->Iex.RdTmp.tmp);
        }
        taint_addr(addr);
        VG_(printf)("0x%x 0x%x DD\n",addr,0);
    }
    else if(is_addr_tainted(addr)){
        untaint_addr(addr);
    }
    return;
}
static VG_REGPARM(2) void taint_runtime_bore(Addr addr, UInt data)
{
}
/*------------------------------------------------------------*/
/*--- Basic tool functions                                 ---*/
/*------------------------------------------------------------*/

static void tg_post_clo_init(void)
{
    init_shadow_memory();
}

static
IRSB* tg_instrument ( VgCallbackClosure* closure,
                      IRSB* sbIn,
                      VexGuestLayout* layout, 
                      VexGuestExtents* vge,
                      IRType gWordTy, IRType hWordTy )
{
    IRDirty*   di;
    Int        i;
    IRSB*      sbOut;
    IRType     type;
    IRTypeEnv* tyenv = sbIn->tyenv;
    IRExpr**   argv;
    Int        offset;
    IRExpr     *data, *addr, *dataexpr, *addrexpr;
    IRTemp     tmp;
    char *fnname = global_fnname;
    if (gWordTy != hWordTy) {
        /* We don't currently support this case. */
        VG_(tool_panic)("host/guest word size mismatch");
    }

    /* Set up SB */
    sbOut = deepCopyIRSBExceptStmts(sbIn);

    // Copy verbatim any IR preamble preceding the first IMark
    i = 0;
    while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
        addStmtToIRSB( sbOut, sbIn->stmts[i] );
        i++;
    }
    for (/*use current i*/; i < sbIn->stmts_used; i++) {
        IRStmt* st = sbIn->stmts[i];
        if (!st || st->tag == Ist_NoOp) continue;

        /* Prettyprint All IR statements Starting from main
           that valgrind has generated */
        /*if(clo_trace_mem){
            ppIRStmt(st);
            VG_(printf)("\n");
        }
        */

        switch (st->tag) {
           case Ist_NoOp:
           case Ist_AbiHint:
           case Ist_MBE:
              addStmtToIRSB( sbOut, st );
              break;

           case Ist_Put:
              if(clo_trace_mem){
                  offset  = st->Ist.Put.offset;
                  data = tg_deepCopyIRExpr(st->Ist.Put.data);
                  //data = st->Ist.Put.data;
                  tl_assert(isIRAtom(data));
                 //VG_(printf)("Data address(%d) is 0x%x\n",put_count,data);
                 argv = mkIRExprVec_3( mkIRExpr_HWord((HWord)offset), mkIRExpr_HWord( (HWord)data),mkIRExpr_HWord( (HWord)put_count));
                 di   = unsafeIRDirty_0_N( /*regparms*/3, 
                                   "taint_runtime_put", VG_(fnptr_to_fnentry)(taint_runtime_put),
                                    argv );
                 addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
                 put_count++;
              }
              addStmtToIRSB( sbOut, st );
           break;
           case Ist_PutI:
              if (clo_trace_mem) {
                VG_(printf)("PutI instruction. Ignoring.");
              }
              addStmtToIRSB( sbOut, st );
           break;
           case Ist_IMark:
              if (VG_(get_fnname_if_entry)(
                                            st->Ist.IMark.addr, 
                                            fnname, 100)){
                   //VG_(printf)("-- %s --\n",fnname);
                   if(0 == VG_(strcmp)(fnname, "main")) {
                      clo_trace_mem = True;
                  }
                  if(0 == VG_(strcmp)(fnname, "exit")) {
                      clo_trace_mem = False;
                  }
               }
              addStmtToIRSB( sbOut, st );
              break;

           case Ist_WrTmp:
              if (clo_trace_mem) {
                 data = st->Ist.WrTmp.data;
                 dataexpr = tg_deepCopyIRExpr(st->Ist.WrTmp.data);
                 tmp = st->Ist.WrTmp.tmp;
                 addr = NULL;
                 if (data->tag == Iex_Load) {
                    addrexpr = tg_deepCopyIRExpr(data->Iex.Load.addr);
                    addr = data->Iex.Load.addr;
                 }
                 if(addr!=NULL)
                    argv = mkIRExprVec_3( mkIRExpr_HWord((HWord)tmp), mkIRExpr_HWord( (HWord)dataexpr), addr);
                 else
                    argv = mkIRExprVec_3( mkIRExpr_HWord((HWord)tmp), mkIRExpr_HWord( (HWord)dataexpr),  
                                          mkIRExpr_HWord((HWord)NULL));
                    di   = unsafeIRDirty_0_N( /*regparms*/3, 
                                   "taint_runtime_wrtmp", VG_(fnptr_to_fnentry)(taint_runtime_wrtmp),
                                    argv );
                 addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
              }
              addStmtToIRSB( sbOut, st );
              break;

           case Ist_Store:
              if (clo_trace_mem) {
                 //VG_(printf)("Store instrumentation time\n");
                 data  = st->Ist.Store.data;
                 //tl_assert(typeOfIRExpr(sbIn->tyenv,data)==Ity_I32);
                 addr  = st->Ist.Store.addr;
                 //tl_assert(typeOfIRExpr(sbIn->tyenv,addr)==Ity_I32);
                 dataexpr  = tg_deepCopyIRExpr(st->Ist.Store.data);
                 addrexpr  = tg_deepCopyIRExpr(st->Ist.Store.addr);
                 tl_assert(isIRAtom(data));
                 if(typeOfIRExpr(sbIn->tyenv,data)!=Ity_I32){
                    IRExpr *newex = widenUto32(sbIn,data);
                    if(newex!=NULL){
                        IRTemp newtemp = newIRTemp(sbOut->tyenv,Ity_I32);
                        IRStmt *wrtmpst = IRStmt_WrTmp (newtemp,newex);
                        addStmtToIRSB(sbOut,wrtmpst);
                        IRExpr *rdtmpexpr = IRExpr_RdTmp(newtemp);
                        argv = mkIRExprVec_4( addr, rdtmpexpr, 
                                mkIRExpr_HWord((HWord)addrexpr), mkIRExpr_HWord( (HWord)dataexpr));
                        di   = unsafeIRDirty_0_N( /*regparms*/3, 
                                       "taint_runtime_store", VG_(fnptr_to_fnentry)(taint_runtime_store),
                                        argv );
                    }
                    else {
                        argv = mkIRExprVec_3( addr,mkIRExpr_HWord((HWord)addrexpr), 
                                              mkIRExpr_HWord( (HWord)dataexpr));
                        di   = unsafeIRDirty_0_N( /*regparms*/3, 
                                       "taint_runtime_store_special", VG_(fnptr_to_fnentry)(taint_runtime_store_special),
                                        argv );
                    }
                 }
                 else {
                        argv = mkIRExprVec_4( addr, data, 
                                mkIRExpr_HWord((HWord)addrexpr), mkIRExpr_HWord( (HWord)dataexpr));
                        di   = unsafeIRDirty_0_N( 3, 
                                       "taint_runtime_store", VG_(fnptr_to_fnentry)(taint_runtime_store),
                                        argv );
                        /*argv = mkIRExprVec_2( addr, data);
                        di   = unsafeIRDirty_0_N( 2, 
                                       "taint_runtime_bore", VG_(fnptr_to_fnentry)(taint_runtime_bore),
                                        argv );*/
                 }
                 addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
              }
              addStmtToIRSB( sbOut, st );
              break;

           case Ist_Dirty: {
              if (clo_trace_mem) {
                 Int      dsize;
                 IRDirty* d = st->Ist.Dirty.details;
                 VG_(printf)("Dirty instruction. Ignoring.");
              }
              addStmtToIRSB( sbOut, st );
              break;
           }

           case Ist_CAS: {
              /* We treat it as a read and a write of the location.  I
                 think that is the same behaviour as it was before IRCAS
                 was introduced, since prior to that point, the Vex
                 front ends would translate a lock-prefixed instruction
                 into a (normal) read followed by a (normal) write. */
              if (clo_trace_mem) {
                VG_(printf)("CAS instruction. Ignoring.");
              }
              addStmtToIRSB( sbOut, st );
              break;
           }

           case Ist_LLSC: {
              if (clo_trace_mem) {
                VG_(printf)("LLSC instruction. Ignoring.");
              }
              addStmtToIRSB( sbOut, st );
              break;
           }

           case Ist_Exit:
              if (clo_trace_mem) {
              }
              addStmtToIRSB( sbOut, st );      // Original statement
              break;

           default:
              tl_assert(0);
        }
    }
    return sbOut;
}

static void tg_fini(Int exitcode)
{
}

static void tg_pre_clo_init(void)
{
   VG_(details_name)            ("Taintgrind");
   VG_(details_version)         ("0.1");
   VG_(details_description)     ("CS510 Valgrind tool");
   VG_(details_copyright_author)(
      "Copyright (C) 2002-2011, and GNU GPL'd, by gogo");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(details_avg_translation_sizeB) ( 275 );

   VG_(needs_syscall_wrapper)   (pre_read,post_read);

   VG_(basic_tool_funcs)        (tg_post_clo_init,
                                 tg_instrument,
                                 tg_fini);

   /* No needs, no core events to track */
}

VG_DETERMINE_INTERFACE_VERSION(tg_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
