package com.sschr15.z3kt

import kotlinx.cinterop.toKString
import lib.z3.*

@PublishedApi
internal actual fun initialize() {
    // nothing to do
}

public actual open class Z3Exception(message: String) : Exception(message)

public actual abstract class Z3Object {
    public override fun toString(): String {
        throw NotImplementedError("toString needs to be overridden!")
    }
}

public actual open class Symbol(internal val native: Z3_symbol, internal val context: Context) : Z3Object() {
    public override fun toString(): String = Z3_get_symbol_string(context.native, native)!!.toKString()
}

public actual class IntSymbol(native: Z3_symbol, context: Context) : Symbol(native, context)
public actual class StringSymbol(native: Z3_symbol, context: Context) : Symbol(native, context)

public actual class Constructor<R>(internal val native: Z3_constructor) : Z3Object()
public actual class ConstructorList<R>(internal val native: Z3_constructor_list) : Z3Object()

public actual class ASTVector(internal val native: MutableList<Z3_ast>) : Z3Object()

context(ctx: Context) internal fun <S : Sort> Expr(native: Z3_ast): Expr<S> = Expr(native, ctx)

public actual class BoolExpr(native: Z3_ast, context: Context) : Expr<BoolSort>(context, native)
public actual open class ArithExpr<S : ArithSort>(native: Z3_ast, context: Context) : Expr<S>(context, native)
public actual open class IntExpr(native: Z3_ast, context: Context) : ArithExpr<IntSort>(native, context)
public actual open class RealExpr(native: Z3_ast, context: Context) : ArithExpr<RealSort>(native, context)
public actual open class BitVecExpr(native: Z3_ast, context: Context) : Expr<BitVecSort>(context, native)
public actual open class ArrayExpr<D : Sort, R : Sort>(native: Z3_ast, context: Context) : Expr<ArraySort<D, R>>(context, native)
public actual class SeqExpr<R : Sort>(native: Z3_ast, context: Context) : Expr<SeqSort<R>>(context, native)
public actual class ReExpr<R : Sort>(native: Z3_ast, context: Context) : Expr<ReSort<R>>(context, native)
public actual open class FPExpr(native: Z3_ast, context: Context) : Expr<FPSort>(context, native)
public actual open class FPRMExpr(native: Z3_ast, context: Context) : Expr<FPRMSort>(context, native)

public actual class IntNum(native: Z3_ast, context: Context) : IntExpr(native, context)
public actual class RatNum(native: Z3_ast, context: Context) : RealExpr(native, context)
public actual class BitVecNum(native: Z3_ast, context: Context) : BitVecExpr(native, context)
public actual class FPNum(native: Z3_ast, context: Context) : FPExpr(native, context)
public actual class FPRMNum(native: Z3_ast, context: Context) : FPRMExpr(native, context)

public actual class Lambda<R : Sort>(native: Z3_ast, context: Context) : ArrayExpr<Sort, R>(native, context) {
    public actual override fun translate(otherContext: Context): Lambda<R> = Lambda(Z3_translate(context.native, native, otherContext.native)!!, otherContext)
}

public actual class Quantifier(native: Z3_ast, context: Context) : Expr<BoolSort>(context, native) {
    public actual override fun translate(otherContext: Context): Quantifier = Quantifier(Z3_translate(context.native, native, otherContext.native)!!, otherContext)
}

context(ctx: Context) internal fun BoolExpr(native: Z3_ast): BoolExpr = BoolExpr(native, ctx)
context(ctx: Context) internal fun IntExpr(native: Z3_ast): IntExpr = IntExpr(native, ctx)
context(ctx: Context) internal fun RealExpr(native: Z3_ast): RealExpr = RealExpr(native, ctx)
context(ctx: Context) internal fun BitVecExpr(native: Z3_ast): BitVecExpr = BitVecExpr(native, ctx)
context(ctx: Context) internal fun <D : Sort, R : Sort> ArrayExpr(native: Z3_ast): ArrayExpr<D, R> = ArrayExpr(native, ctx)
context(ctx: Context) internal fun <R : Sort> SeqExpr(native: Z3_ast): SeqExpr<R> = SeqExpr(native, ctx)
context(ctx: Context) internal fun <R : Sort> ReExpr(native: Z3_ast): ReExpr<R> = ReExpr(native, ctx)
context(ctx: Context) internal fun FPExpr(native: Z3_ast): FPExpr = FPExpr(native, ctx)
context(ctx: Context) internal fun FPRMExpr(native: Z3_ast): FPRMExpr = FPRMExpr(native, ctx)
context(ctx: Context) internal fun IntNum(native: Z3_ast): IntNum = IntNum(native, ctx)
context(ctx: Context) internal fun RatNum(native: Z3_ast): RatNum = RatNum(native, ctx)
context(ctx: Context) internal fun BitVecNum(native: Z3_ast): BitVecNum = BitVecNum(native, ctx)
context(ctx: Context) internal fun FPNum(native: Z3_ast): FPNum = FPNum(native, ctx)
context(ctx: Context) internal fun FPRMNum(native: Z3_ast): FPRMNum = FPRMNum(native, ctx)
context(ctx: Context) internal fun <R : Sort> Lambda(native: Z3_ast): Lambda<R> = Lambda(native, ctx)
context(ctx: Context) internal fun Quantifier(native: Z3_ast): Quantifier = Quantifier(native, ctx)

public actual class FuncDecl<R : Sort>(internal val native: Z3_func_decl, context: Context) : AST(context, Z3_func_decl_to_ast(context.native, native)!!)
public actual class Pattern(internal val native: Z3_pattern) : Z3Object()
public actual class Tactic(internal val native: Z3_tactic) : Z3Object()
public actual class Probe(internal val native: Z3_probe) : Z3Object()
public actual class Goal(internal val native: Z3_goal) : Z3Object()
public actual class ApplyResult(internal val native: Z3_apply_result) : Z3Object()
public actual class Params(internal val native: Z3_params) : Z3Object()
public actual class ParamDescriptions(internal val native: Z3_param_descrs) : Z3Object()
public actual class Simplifier(internal val native: Z3_simplifier) : Z3Object()
public actual class Fixedpoint(internal val native: Z3_fixedpoint) : Z3Object()

public actual class FuncInterp<R : Sort>(internal val native: Z3_func_interp) : Z3Object() {
    public actual class Entry<R : Sort>(internal val native: Z3_func_entry) : Z3Object()
}

public actual typealias AstPrintMode = lib.z3.Z3_ast_print_mode

context(ctx: Context) internal fun <R : Sort> FuncDecl(native: Z3_func_decl): FuncDecl<R> = FuncDecl(native, ctx)

public actual enum class Status {
    UNKNOWN,
    UNSATISFIABLE,
    SATISFIABLE
}
