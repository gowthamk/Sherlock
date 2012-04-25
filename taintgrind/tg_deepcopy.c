#include "tg_include.h"

/*---------------------------------------------------------------*/
/*--- Constructors                                            ---*/
/*---------------------------------------------------------------*/

/* Constructors -- IRConst */

static IRConst* tg_IRConst_U1 ( Bool bit )
{
   IRConst* c = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag     = Ico_U1;
   c->Ico.U1  = bit;
   /* call me paranoid; I don't care :-) */
   tl_assert(bit == False || bit == True);
   return c;
}
static IRConst* tg_IRConst_U8 ( UChar u8 )
{
   IRConst* c = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag     = Ico_U8;
   c->Ico.U8  = u8;
   return c;
}
static IRConst* tg_IRConst_U16 ( UShort u16 )
{
   IRConst* c = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag     = Ico_U16;
   c->Ico.U16 = u16;
   return c;
}
static IRConst* tg_IRConst_U32 ( UInt u32 )
{
   IRConst* c = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag     = Ico_U32;
   c->Ico.U32 = u32;
   return c;
}
static IRConst* tg_IRConst_U64 ( ULong u64 )
{
   IRConst* c = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag     = Ico_U64;
   c->Ico.U64 = u64;
   return c;
}
static IRConst* tg_IRConst_F32 ( Float f32 )
{
   IRConst* c = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag     = Ico_F32;
   c->Ico.F32 = f32;
   return c;
}
static IRConst* tg_IRConst_F32i ( UInt f32i )
{
   IRConst* c  = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag      = Ico_F32i;
   c->Ico.F32i = f32i;
   return c;
}
static IRConst* tg_IRConst_F64 ( Double f64 )
{
   IRConst* c = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag     = Ico_F64;
   c->Ico.F64 = f64;
   return c;
}
static IRConst* tg_IRConst_F64i ( ULong f64i )
{
   IRConst* c  = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag      = Ico_F64i;
   c->Ico.F64i = f64i;
   return c;
}
static IRConst* tg_IRConst_V128 ( UShort con )
{
   IRConst* c  = VG_(malloc)("deepcopy",sizeof(IRConst));
   c->tag      = Ico_V128;
   c->Ico.V128 = con;
   return c;
}

/* Constructors -- IRCallee */

static IRCallee* tg_mkIRCallee ( Int regparms, HChar* name, void* addr )
{
   IRCallee* ce = VG_(malloc)("deepcopy",sizeof(IRCallee));
   ce->regparms = regparms;
   ce->name     = name;
   ce->addr     = addr;
   ce->mcx_mask = 0;
   tl_assert(regparms >= 0 && regparms <= 3);
   tl_assert(name != NULL);
   tl_assert(addr != 0);
   return ce;
}


/* Constructors -- IRRegArray */

static IRRegArray* tg_mkIRRegArray ( Int base, IRType elemTy, Int nElems )
{
   IRRegArray* arr = VG_(malloc)("deepcopy",sizeof(IRRegArray));
   arr->base       = base;
   arr->elemTy     = elemTy;
   arr->nElems     = nElems;
   tl_assert(!(arr->base < 0 || arr->base > 10000 /* somewhat arbitrary */));
   tl_assert(!(arr->elemTy == Ity_I1));
   tl_assert(!(arr->nElems <= 0 || arr->nElems > 500 /* somewhat arbitrary */));
   return arr;
}

/* Constructors -- IRExpr */

static IRExpr* tg_IRExpr_Binder ( Int binder ) {
   IRExpr* e            = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag               = Iex_Binder;
   e->Iex.Binder.binder = binder;
   return e;
}
static IRExpr* tg_IRExpr_Get ( Int off, IRType ty ) {
   IRExpr* e         = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag            = Iex_Get;
   e->Iex.Get.offset = off;
   e->Iex.Get.ty     = ty;
   return e;
}
static IRExpr* tg_IRExpr_GetI ( IRRegArray* descr, IRExpr* ix, Int bias ) {
   IRExpr* e         = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag            = Iex_GetI;
   e->Iex.GetI.descr = descr;
   e->Iex.GetI.ix    = ix;
   e->Iex.GetI.bias  = bias;
   return e;
}
static IRExpr* tg_IRExpr_RdTmp ( IRTemp tmp ) {
   IRExpr* e        = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag           = Iex_RdTmp;
   e->Iex.RdTmp.tmp = tmp;
   return e;
}
static IRExpr* tg_IRExpr_Qop ( IROp op, IRExpr* arg1, IRExpr* arg2, 
                              IRExpr* arg3, IRExpr* arg4 ) {
   IRExpr* e       = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag          = Iex_Qop;
   e->Iex.Qop.op   = op;
   e->Iex.Qop.arg1 = arg1;
   e->Iex.Qop.arg2 = arg2;
   e->Iex.Qop.arg3 = arg3;
   e->Iex.Qop.arg4 = arg4;
   return e;
}
static IRExpr* tg_IRExpr_Triop  ( IROp op, IRExpr* arg1, 
                                 IRExpr* arg2, IRExpr* arg3 ) {
   IRExpr* e         = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag            = Iex_Triop;
   e->Iex.Triop.op   = op;
   e->Iex.Triop.arg1 = arg1;
   e->Iex.Triop.arg2 = arg2;
   e->Iex.Triop.arg3 = arg3;
   return e;
}
static IRExpr* tg_IRExpr_Binop ( IROp op, IRExpr* arg1, IRExpr* arg2 ) {
   IRExpr* e         = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag            = Iex_Binop;
   e->Iex.Binop.op   = op;
   e->Iex.Binop.arg1 = arg1;
   e->Iex.Binop.arg2 = arg2;
   return e;
}
static IRExpr* tg_IRExpr_Unop ( IROp op, IRExpr* arg ) {
   IRExpr* e       = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag          = Iex_Unop;
   e->Iex.Unop.op  = op;
   e->Iex.Unop.arg = arg;
   return e;
}
static IRExpr* tg_IRExpr_Load ( IREndness end, IRType ty, IRExpr* addr ) {
   IRExpr* e        = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag           = Iex_Load;
   e->Iex.Load.end  = end;
   e->Iex.Load.ty   = ty;
   e->Iex.Load.addr = addr;
   tl_assert(end == Iend_LE || end == Iend_BE);
   return e;
}
static IRExpr* tg_IRExpr_Const ( IRConst* con ) {
   IRExpr* e        = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag           = Iex_Const;
   e->Iex.Const.con = con;
   return e;
}
static IRExpr* tg_IRExpr_CCall ( IRCallee* cee, IRType retty, IRExpr** args ) {
   IRExpr* e          = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag             = Iex_CCall;
   e->Iex.CCall.cee   = cee;
   e->Iex.CCall.retty = retty;
   e->Iex.CCall.args  = args;
   return e;
}
static IRExpr* tg_IRExpr_Mux0X ( IRExpr* cond, IRExpr* expr0, IRExpr* exprX ) {
   IRExpr* e          = VG_(malloc)("deepcopy",sizeof(IRExpr));
   e->tag             = Iex_Mux0X;
   e->Iex.Mux0X.cond  = cond;
   e->Iex.Mux0X.expr0 = expr0;
   e->Iex.Mux0X.exprX = exprX;
   return e;
}



static IRExpr** tg_shallowCopyIRExprVec ( IRExpr** vec )
{
   Int      i;
   IRExpr** newvec;
   for (i = 0; vec[i]; i++)
      ;
   newvec = VG_(malloc)("deepcopy",(i+1)*sizeof(IRExpr*));
   for (i = 0; vec[i]; i++)
      newvec[i] = vec[i];
   newvec[i] = NULL;
   return newvec;
}

/* Deep copy of an IRExpr vector */

static IRExpr** tg_deepCopyIRExprVec ( IRExpr** vec )
{
   Int      i;
   IRExpr** newvec =tg_shallowCopyIRExprVec( vec );
   for (i = 0; newvec[i]; i++)
      newvec[i] = tg_deepCopyIRExpr(newvec[i]);
   return newvec;
}

static IRConst* tg_deepCopyIRConst ( IRConst* c )
{
   switch (c->tag) {
      case Ico_U1:   return tg_IRConst_U1(c->Ico.U1);
      case Ico_U8:   return tg_IRConst_U8(c->Ico.U8);
      case Ico_U16:  return tg_IRConst_U16(c->Ico.U16);
      case Ico_U32:  return tg_IRConst_U32(c->Ico.U32);
      case Ico_U64:  return tg_IRConst_U64(c->Ico.U64);
      case Ico_F32:  return tg_IRConst_F32(c->Ico.F32);
      case Ico_F32i: return tg_IRConst_F32i(c->Ico.F32i);
      case Ico_F64:  return tg_IRConst_F64(c->Ico.F64);
      case Ico_F64i: return tg_IRConst_F64i(c->Ico.F64i);
      case Ico_V128: return tg_IRConst_V128(c->Ico.V128);
      default: VG_(tool_panic)("deepCopyIRConst");
   }
}

static IRCallee* tg_deepCopyIRCallee ( IRCallee* ce )
{
   IRCallee* ce2 = tg_mkIRCallee(ce->regparms, ce->name, ce->addr);
   ce2->mcx_mask = ce->mcx_mask;
   return ce2;
}

static IRRegArray* tg_deepCopyIRRegArray ( IRRegArray* d )
{
   return tg_mkIRRegArray(d->base, d->elemTy, d->nElems);
}

IRExpr* tg_deepCopyIRExpr ( IRExpr* e )
{
   switch (e->tag) {
      case Iex_Get: 
         return tg_IRExpr_Get(e->Iex.Get.offset, e->Iex.Get.ty);
      case Iex_GetI: 
         return tg_IRExpr_GetI(tg_deepCopyIRRegArray(e->Iex.GetI.descr), 
                            tg_deepCopyIRExpr(e->Iex.GetI.ix),
                            e->Iex.GetI.bias);
      case Iex_RdTmp: 
         return tg_IRExpr_RdTmp(e->Iex.RdTmp.tmp);
      case Iex_Qop: 
         return tg_IRExpr_Qop(e->Iex.Qop.op,
                           tg_deepCopyIRExpr(e->Iex.Qop.arg1),
                           tg_deepCopyIRExpr(e->Iex.Qop.arg2),
                           tg_deepCopyIRExpr(e->Iex.Qop.arg3),
                           tg_deepCopyIRExpr(e->Iex.Qop.arg4));
      case Iex_Triop: 
         return tg_IRExpr_Triop(e->Iex.Triop.op,
                             tg_deepCopyIRExpr(e->Iex.Triop.arg1),
                             tg_deepCopyIRExpr(e->Iex.Triop.arg2),
                             tg_deepCopyIRExpr(e->Iex.Triop.arg3));
      case Iex_Binop: 
         return tg_IRExpr_Binop(e->Iex.Binop.op,
                             tg_deepCopyIRExpr(e->Iex.Binop.arg1),
                             tg_deepCopyIRExpr(e->Iex.Binop.arg2));
      case Iex_Unop: 
         return tg_IRExpr_Unop(e->Iex.Unop.op,
                            tg_deepCopyIRExpr(e->Iex.Unop.arg));
      case Iex_Load: 
         return tg_IRExpr_Load(e->Iex.Load.end,
                            e->Iex.Load.ty,
                            tg_deepCopyIRExpr(e->Iex.Load.addr));
      case Iex_Const: 
         return tg_IRExpr_Const(tg_deepCopyIRConst(e->Iex.Const.con));
      case Iex_CCall:
         return tg_IRExpr_CCall(tg_deepCopyIRCallee(e->Iex.CCall.cee),
                             e->Iex.CCall.retty,
                             tg_deepCopyIRExprVec(e->Iex.CCall.args));

      case Iex_Mux0X: 
         return tg_IRExpr_Mux0X(tg_deepCopyIRExpr(e->Iex.Mux0X.cond),
                             tg_deepCopyIRExpr(e->Iex.Mux0X.expr0),
                             tg_deepCopyIRExpr(e->Iex.Mux0X.exprX));
      default:
         VG_(tool_panic)("tg_deepCopyIRExpr");
   }
}
