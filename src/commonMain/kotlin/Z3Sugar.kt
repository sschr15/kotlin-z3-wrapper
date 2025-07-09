@file:Suppress("UNCHECKED_CAST", "FunctionName", "DANGEROUS_CHARACTERS", "ERROR_SUPPRESSION")

package com.sschr15.z3kt

import kotlin.jvm.JvmName

public val <S : Sort> Expr<S>.sort: S get() = getSort()
public val BitVecSort.size: Int get() = getSize()

//region: Comparisons
context(context: Context) public infix fun <T : Sort> Expr<T>.eq(other: Expr<T>): BoolExpr = context.mkEq(this, other)
context(context: Context) public infix fun <T : Sort> Expr<T>.neq(other: Expr<T>): BoolExpr = context.mkNot(context.mkEq(this, other))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.lt(other: Expr<T>): BoolExpr = context.mkLt(this, other)
context(context: Context) public infix fun <T : ArithSort> Expr<T>.gt(other: Expr<T>): BoolExpr = context.mkGt(this, other)
context(context: Context) public infix fun <T : ArithSort> Expr<T>.lte(other: Expr<T>): BoolExpr = context.mkLe(this, other)
context(context: Context) public infix fun <T : ArithSort> Expr<T>.gte(other: Expr<T>): BoolExpr = context.mkGe(this, other)

context(context: Context) public infix fun <T : ArithSort> Expr<T>.eq(other: Int): BoolExpr = context.mkEq(this, context.mkInt(other))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.neq(other: Int): BoolExpr = context.mkNot(context.mkEq(this, context.mkInt(other)))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.lt(other: Int): BoolExpr = context.mkLt(this, context.mkInt(other))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.gt(other: Int): BoolExpr = context.mkGt(this, context.mkInt(other))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.lte(other: Int): BoolExpr = context.mkLe(this, context.mkInt(other))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.gte(other: Int): BoolExpr = context.mkGe(this, context.mkInt(other))

context(context: Context) public infix fun <T : ArithSort> Expr<T>.eq(other: Long): BoolExpr = context.mkEq(this, context.mkInt(other))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.neq(other: Long): BoolExpr = context.mkNot(context.mkEq(this, context.mkInt(other)))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.lt(other: Long): BoolExpr = context.mkLt(this, context.mkInt(other))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.gt(other: Long): BoolExpr = context.mkGt(this, context.mkInt(other))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.lte(other: Long): BoolExpr = context.mkLe(this, context.mkInt(other))
context(context: Context) public infix fun <T : ArithSort> Expr<T>.gte(other: Long): BoolExpr = context.mkGe(this, context.mkInt(other))

context(context: Context) public infix fun <T : ArithSort> Int.eq(other: Expr<T>): BoolExpr = context.mkEq(context.mkInt(this), other)
context(context: Context) public infix fun <T : ArithSort> Int.neq(other: Expr<T>): BoolExpr = context.mkNot(context.mkEq(context.mkInt(this), other))
context(context: Context) public infix fun <T : ArithSort> Int.lt(other: Expr<T>): BoolExpr = context.mkLt(context.mkInt(this), other)
context(context: Context) public infix fun <T : ArithSort> Int.gt(other: Expr<T>): BoolExpr = context.mkGt(context.mkInt(this), other)
context(context: Context) public infix fun <T : ArithSort> Int.lte(other: Expr<T>): BoolExpr = context.mkLe(context.mkInt(this), other)
context(context: Context) public infix fun <T : ArithSort> Int.gte(other: Expr<T>): BoolExpr = context.mkGe(context.mkInt(this), other)

context(context: Context) public infix fun <T : ArithSort> Long.eq(other: Expr<T>): BoolExpr = context.mkEq(context.mkInt(this), other)
context(context: Context) public infix fun <T : ArithSort> Long.neq(other: Expr<T>): BoolExpr = context.mkNot(context.mkEq(context.mkInt(this), other))
context(context: Context) public infix fun <T : ArithSort> Long.lt(other: Expr<T>): BoolExpr = context.mkLt(context.mkInt(this), other)
context(context: Context) public infix fun <T : ArithSort> Long.gt(other: Expr<T>): BoolExpr = context.mkGt(context.mkInt(this), other)
context(context: Context) public infix fun <T : ArithSort> Long.lte(other: Expr<T>): BoolExpr = context.mkLe(context.mkInt(this), other)
context(context: Context) public infix fun <T : ArithSort> Long.gte(other: Expr<T>): BoolExpr = context.mkGe(context.mkInt(this), other)

@JvmName("bvlt") context(context: Context) public infix fun Expr<BitVecSort>.lt(other: Expr<BitVecSort>): BoolExpr = context.mkBVSLT(this, other)
@JvmName("bvgt") context(context: Context) public infix fun Expr<BitVecSort>.gt(other: Expr<BitVecSort>): BoolExpr = context.mkBVSGT(this, other)
@JvmName("bvlte") context(context: Context) public infix fun Expr<BitVecSort>.lte(other: Expr<BitVecSort>): BoolExpr = context.mkBVSLE(this, other)
@JvmName("bvgte") context(context: Context) public infix fun Expr<BitVecSort>.gte(other: Expr<BitVecSort>): BoolExpr = context.mkBVSGE(this, other)
@JvmName("bvult") context(context: Context) public infix fun Expr<BitVecSort>.ult(other: Expr<BitVecSort>): BoolExpr = context.mkBVULT(this, other)
@JvmName("bvugt") context(context: Context) public infix fun Expr<BitVecSort>.ugt(other: Expr<BitVecSort>): BoolExpr = context.mkBVUGT(this, other)
@JvmName("bvulte") context(context: Context) public infix fun Expr<BitVecSort>.ulte(other: Expr<BitVecSort>): BoolExpr = context.mkBVULE(this, other)
@JvmName("bvugte") context(context: Context) public infix fun Expr<BitVecSort>.ugte(other: Expr<BitVecSort>): BoolExpr = context.mkBVUGE(this, other)

@JvmName("bvEq") context(context: Context) public infix fun Expr<BitVecSort>.eq(other: Int): BoolExpr = context.mkEq(this, context.mkBV(other, sort.size))
@JvmName("bvNeq") context(context: Context) public infix fun Expr<BitVecSort>.neq(other: Int): BoolExpr = context.mkNot(context.mkEq(this, context.mkBV(other, sort.size)))
@JvmName("bvlt") context(context: Context) public infix fun Expr<BitVecSort>.lt(other: Int): BoolExpr = context.mkBVSLT(this, context.mkBV(other, sort.size))
@JvmName("bvgt") context(context: Context) public infix fun Expr<BitVecSort>.gt(other: Int): BoolExpr = context.mkBVSGT(this, context.mkBV(other, sort.size))
@JvmName("bvlte") context(context: Context) public infix fun Expr<BitVecSort>.lte(other: Int): BoolExpr = context.mkBVSLE(this, context.mkBV(other, sort.size))
@JvmName("bvgte") context(context: Context) public infix fun Expr<BitVecSort>.gte(other: Int): BoolExpr = context.mkBVSGE(this, context.mkBV(other, sort.size))
@JvmName("bvult") context(context: Context) public infix fun Expr<BitVecSort>.ult(other: Int): BoolExpr = context.mkBVULT(this, context.mkBV(other, sort.size))
@JvmName("bvugt") context(context: Context) public infix fun Expr<BitVecSort>.ugt(other: Int): BoolExpr = context.mkBVUGT(this, context.mkBV(other, sort.size))
@JvmName("bvulte") context(context: Context) public infix fun Expr<BitVecSort>.ulte(other: Int): BoolExpr = context.mkBVULE(this, context.mkBV(other, sort.size))
@JvmName("bvugte") context(context: Context) public infix fun Expr<BitVecSort>.ugte(other: Int): BoolExpr = context.mkBVUGE(this, context.mkBV(other, sort.size))

@JvmName("bveq") context(context: Context) public infix fun Expr<BitVecSort>.eq(other: Long): BoolExpr = context.mkEq(this, context.mkBV(other, sort.size))
@JvmName("bvneq") context(context: Context) public infix fun Expr<BitVecSort>.neq(other: Long): BoolExpr = context.mkNot(context.mkEq(this, context.mkBV(other, sort.size)))
@JvmName("bvlt") context(context: Context) public infix fun Expr<BitVecSort>.lt(other: Long): BoolExpr = context.mkBVSLT(this, context.mkBV(other, sort.size))
@JvmName("bvgt") context(context: Context) public infix fun Expr<BitVecSort>.gt(other: Long): BoolExpr = context.mkBVSGT(this, context.mkBV(other, sort.size))
@JvmName("bvlte") context(context: Context) public infix fun Expr<BitVecSort>.lte(other: Long): BoolExpr = context.mkBVSLE(this, context.mkBV(other, sort.size))
@JvmName("bvgte") context(context: Context) public infix fun Expr<BitVecSort>.gte(other: Long): BoolExpr = context.mkBVSGE(this, context.mkBV(other, sort.size))
@JvmName("bvult") context(context: Context) public infix fun Expr<BitVecSort>.ult(other: Long): BoolExpr = context.mkBVULT(this, context.mkBV(other, sort.size))
@JvmName("bvugt") context(context: Context) public infix fun Expr<BitVecSort>.ugt(other: Long): BoolExpr = context.mkBVUGT(this, context.mkBV(other, sort.size))
@JvmName("bvulte") context(context: Context) public infix fun Expr<BitVecSort>.ulte(other: Long): BoolExpr = context.mkBVULE(this, context.mkBV(other, sort.size))
@JvmName("bvugte") context(context: Context) public infix fun Expr<BitVecSort>.ugte(other: Long): BoolExpr = context.mkBVUGE(this, context.mkBV(other, sort.size))

@JvmName("bveq") context(context: Context) public infix fun Int.eq(other: Expr<BitVecSort>): BoolExpr = context.mkEq(context.mkBV(this, other.sort.size), other)
@JvmName("bvneq") context(context: Context) public infix fun Int.neq(other: Expr<BitVecSort>): BoolExpr = context.mkNot(context.mkEq(context.mkBV(this, other.sort.size), other))
@JvmName("bvlt") context(context: Context) public infix fun Int.lt(other: Expr<BitVecSort>): BoolExpr = context.mkBVSLT(context.mkBV(this, other.sort.size), other)
@JvmName("bvgt") context(context: Context) public infix fun Int.gt(other: Expr<BitVecSort>): BoolExpr = context.mkBVSGT(context.mkBV(this, other.sort.size), other)
@JvmName("bvlte") context(context: Context) public infix fun Int.lte(other: Expr<BitVecSort>): BoolExpr = context.mkBVSLE(context.mkBV(this, other.sort.size), other)
@JvmName("bvgte") context(context: Context) public infix fun Int.gte(other: Expr<BitVecSort>): BoolExpr = context.mkBVSGE(context.mkBV(this, other.sort.size), other)
@JvmName("bvult") context(context: Context) public infix fun Int.ult(other: Expr<BitVecSort>): BoolExpr = context.mkBVULT(context.mkBV(this, other.sort.size), other)
@JvmName("bvugt") context(context: Context) public infix fun Int.ugt(other: Expr<BitVecSort>): BoolExpr = context.mkBVUGT(context.mkBV(this, other.sort.size), other)
@JvmName("bvulte") context(context: Context) public infix fun Int.ulte(other: Expr<BitVecSort>): BoolExpr = context.mkBVULE(context.mkBV(this, other.sort.size), other)
@JvmName("bvugte") context(context: Context) public infix fun Int.ugte(other: Expr<BitVecSort>): BoolExpr = context.mkBVUGE(context.mkBV(this, other.sort.size), other)

@JvmName("bveq") context(context: Context) public infix fun Long.eq(other: Expr<BitVecSort>): BoolExpr = context.mkEq(context.mkBV(this, other.sort.size), other)
@JvmName("bvneq") context(context: Context) public infix fun Long.neq(other: Expr<BitVecSort>): BoolExpr = context.mkNot(context.mkEq(context.mkBV(this, other.sort.size), other))
@JvmName("bvlt") context(context: Context) public infix fun Long.lt(other: Expr<BitVecSort>): BoolExpr = context.mkBVSLT(context.mkBV(this, other.sort.size), other)
@JvmName("bvgt") context(context: Context) public infix fun Long.gt(other: Expr<BitVecSort>): BoolExpr = context.mkBVSGT(context.mkBV(this, other.sort.size), other)
@JvmName("bvlte") context(context: Context) public infix fun Long.lte(other: Expr<BitVecSort>): BoolExpr = context.mkBVSLE(context.mkBV(this, other.sort.size), other)
@JvmName("bvgte") context(context: Context) public infix fun Long.gte(other: Expr<BitVecSort>): BoolExpr = context.mkBVSGE(context.mkBV(this, other.sort.size), other)
@JvmName("bvult") context(context: Context) public infix fun Long.ult(other: Expr<BitVecSort>): BoolExpr = context.mkBVULT(context.mkBV(this, other.sort.size), other)
@JvmName("bvugt") context(context: Context) public infix fun Long.ugt(other: Expr<BitVecSort>): BoolExpr = context.mkBVUGT(context.mkBV(this, other.sort.size), other)
@JvmName("bvulte") context(context: Context) public infix fun Long.ulte(other: Expr<BitVecSort>): BoolExpr = context.mkBVULE(context.mkBV(this, other.sort.size), other)
@JvmName("bvugte") context(context: Context) public infix fun Long.ugte(other: Expr<BitVecSort>): BoolExpr = context.mkBVUGE(context.mkBV(this, other.sort.size), other)

@JvmName("fplt") context(context: Context) public infix fun Expr<FPSort>.lt(other: Expr<FPSort>): BoolExpr = context.mkFPLt(this, other)
@JvmName("fpgt") context(context: Context) public infix fun Expr<FPSort>.gt(other: Expr<FPSort>): BoolExpr = context.mkFPGt(this, other)
@JvmName("fplte") context(context: Context) public infix fun Expr<FPSort>.lte(other: Expr<FPSort>): BoolExpr = context.mkOr(context.mkFPEq(this, other), context.mkFPLt(this, other))
@JvmName("fpgte") context(context: Context) public infix fun Expr<FPSort>.gte(other: Expr<FPSort>): BoolExpr = context.mkOr(context.mkFPEq(this, other), context.mkFPGt(this, other))

@JvmName("fpeq") context(context: Context) public infix fun <S : FPSort> Expr<S>.eq(other: Int): BoolExpr = context.mkFPEq(this as Expr<FPSort>, context.mkFP(other, sort))
@JvmName("fpneq") context(context: Context) public infix fun <S : FPSort> Expr<S>.neq(other: Int): BoolExpr = context.mkNot(context.mkFPEq(this as Expr<FPSort>, context.mkFP(other, sort)))
@JvmName("fplt") context(context: Context) public infix fun <S : FPSort> Expr<S>.lt(other: Int): BoolExpr = context.mkFPLt(this as Expr<FPSort>, context.mkFP(other, sort))
@JvmName("fpgt") context(context: Context) public infix fun <S : FPSort> Expr<S>.gt(other: Int): BoolExpr = context.mkFPGt(this as Expr<FPSort>, context.mkFP(other, sort))
@JvmName("fplte") context(context: Context) public infix fun <S : FPSort> Expr<S>.lte(other: Int): BoolExpr = (this as Expr<FPSort>).lte(context.mkFP(other, sort))
@JvmName("fpgte") context(context: Context) public infix fun <S : FPSort> Expr<S>.gte(other: Int): BoolExpr = (this as Expr<FPSort>).gte(context.mkFP(other, sort))

@JvmName("fpeq") context(context: Context) public infix fun <S : FPSort> Expr<S>.eq(other: Float): BoolExpr = context.mkFPEq(this as Expr<FPSort>, context.mkFP(other, sort))
@JvmName("fpneq") context(context: Context) public infix fun <S : FPSort> Expr<S>.neq(other: Float): BoolExpr = context.mkNot(context.mkFPEq(this as Expr<FPSort>, context.mkFP(other, sort)))
@JvmName("fplt") context(context: Context) public infix fun <S : FPSort> Expr<S>.lt(other: Float): BoolExpr = context.mkFPLt(this as Expr<FPSort>, context.mkFP(other, sort))
@JvmName("fpgt") context(context: Context) public infix fun <S : FPSort> Expr<S>.gt(other: Float): BoolExpr = context.mkFPGt(this as Expr<FPSort>, context.mkFP(other, sort))
@JvmName("fplte") context(context: Context) public infix fun <S : FPSort> Expr<S>.lte(other: Float): BoolExpr = (this as Expr<FPSort>).lte(context.mkFP(other, sort))
@JvmName("fpgte") context(context: Context) public infix fun <S : FPSort> Expr<S>.gte(other: Float): BoolExpr = (this as Expr<FPSort>).gte(context.mkFP(other, sort))

@JvmName("fpeq") context(context: Context) public infix fun <S : FPSort> Expr<S>.eq(other: Double): BoolExpr = context.mkFPEq(this as Expr<FPSort>, context.mkFP(other, sort))
@JvmName("fpneq") context(context: Context) public infix fun <S : FPSort> Expr<S>.neq(other: Double): BoolExpr = context.mkNot(context.mkFPEq(this as Expr<FPSort>, context.mkFP(other, sort)))
@JvmName("fplt") context(context: Context) public infix fun <S : FPSort> Expr<S>.lt(other: Double): BoolExpr = context.mkFPLt(this as Expr<FPSort>, context.mkFP(other, sort))
@JvmName("fpgt") context(context: Context) public infix fun <S : FPSort> Expr<S>.gt(other: Double): BoolExpr = context.mkFPGt(this as Expr<FPSort>, context.mkFP(other, sort))
@JvmName("fplte") context(context: Context) public infix fun <S : FPSort> Expr<S>.lte(other: Double): BoolExpr = (this as Expr<FPSort>).lte(context.mkFP(other, sort))
@JvmName("fpgte") context(context: Context) public infix fun <S : FPSort> Expr<S>.gte(other: Double): BoolExpr = (this as Expr<FPSort>).gte(context.mkFP(other, sort))

context(context: Context) public infix fun BoolExpr.and(other: BoolExpr): BoolExpr = context.mkAnd(this, other)
context(context: Context) public infix fun BoolExpr.or(other: BoolExpr): BoolExpr = context.mkOr(this, other)
context(context: Context) public infix fun BoolExpr.xor(other: BoolExpr): BoolExpr = context.mkXor(this, other)
context(context: Context) public infix fun BoolExpr.implies(other: BoolExpr): BoolExpr = context.mkImplies(this, other)
context(context: Context) public infix fun BoolExpr.iff(other: BoolExpr): BoolExpr = context.mkIff(this, other)
//endregion

//region: Constructions
context(context: Context) public fun int(name: String): IntExpr = context.mkIntConst(name)
context(context: Context) public fun bitVec(name: String, size: Int): BitVecExpr = context.mkBVConst(name, size)
//endregion

//region: Conversions
context(context: Context) public fun Int.toZ3Int(): IntNum = context.mkInt(this)
context(context: Context) public fun Long.toZ3Int(): IntNum = context.mkInt(this)
context(context: Context) public fun Int.toBitVec(bits: Int): BitVecNum = context.mkBV(this, bits)
context(context: Context) public fun Long.toBitVec(bits: Int): BitVecNum = context.mkBV(this, bits)
context(context: Context) public fun IntExpr.toBitVec(bits: Int): BitVecExpr = context.mkInt2BV(bits, this)
context(context: Context) public fun BitVecExpr.toZ3Int(): IntExpr = context.mkBV2Int(this, false)
context(context: Context) public fun IntExpr.toReal(): RealExpr = context.mkInt2Real(this)
context(context: Context) public fun RealExpr.toZ3Int(): IntExpr = context.mkReal2Int(this)

public fun Expr<*>.toInt(): Int = toString().toInt()
public fun Expr<*>.toLong(): Long = toString().toLong()
public fun Expr<*>.toDouble(): Double = toString().toDouble()
public fun Expr<*>.toFloat(): Float = toString().toFloat()
public fun Expr<*>.toBoolean(): Boolean = toString().toBoolean()
//endregion

//region: Operators
context(context: Context) public operator fun <T : ArithSort> Expr<T>.plus(other: Expr<T>): ArithExpr<T> = context.mkAdd(this, other)
context(context: Context) public operator fun <T : ArithSort> Expr<T>.minus(other: Expr<T>): ArithExpr<T> = context.mkSub(this, other)
context(context: Context) public operator fun <T : ArithSort> Expr<T>.times(other: Expr<T>): ArithExpr<T> = context.mkMul(this, other)
context(context: Context) public operator fun <T : ArithSort> Expr<T>.div(other: Expr<T>): ArithExpr<T> = context.mkDiv(this, other)

context(context: Context) public operator fun <T : ArithSort> Expr<T>.unaryMinus(): ArithExpr<T> = context.mkUnaryMinus(this)
context(context: Context) public operator fun Expr<IntSort>.rem(other: Expr<IntSort>): IntExpr = context.mkRem(this, other)

context(context: Context) public operator fun Expr<IntSort>.plus(other: Int): ArithExpr<IntSort> = this + context.mkInt(other)
context(context: Context) public operator fun Expr<IntSort>.minus(other: Int): ArithExpr<IntSort> = this - context.mkInt(other)
context(context: Context) public operator fun Expr<IntSort>.times(other: Int): ArithExpr<IntSort> = this * context.mkInt(other)
context(context: Context) public operator fun Expr<IntSort>.div(other: Int): ArithExpr<IntSort> = this / context.mkInt(other)
context(context: Context) public operator fun Expr<IntSort>.rem(other: Int): IntExpr = this % context.mkInt(other)

context(context: Context) public operator fun Expr<IntSort>.plus(other: Long): ArithExpr<IntSort> = this + context.mkInt(other)
context(context: Context) public operator fun Expr<IntSort>.minus(other: Long): ArithExpr<IntSort> = this - context.mkInt(other)
context(context: Context) public operator fun Expr<IntSort>.times(other: Long): ArithExpr<IntSort> = this * context.mkInt(other)
context(context: Context) public operator fun Expr<IntSort>.div(other: Long): ArithExpr<IntSort> = this / context.mkInt(other)
context(context: Context) public operator fun Expr<IntSort>.rem(other: Long): IntExpr = this % context.mkInt(other)

context(context: Context) public operator fun Int.plus(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkInt(this) + other
context(context: Context) public operator fun Int.minus(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkInt(this) - other
context(context: Context) public operator fun Int.times(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkInt(this) * other
context(context: Context) public operator fun Int.div(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkInt(this) / other
context(context: Context) public operator fun Int.rem(other: Expr<IntSort>): IntExpr = context.mkInt(this) % other

context(context: Context) public operator fun Long.plus(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkInt(this) + other
context(context: Context) public operator fun Long.minus(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkInt(this) - other
context(context: Context) public operator fun Long.times(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkInt(this) * other
context(context: Context) public operator fun Long.div(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkInt(this) / other
context(context: Context) public operator fun Long.rem(other: Expr<IntSort>): IntExpr = context.mkInt(this) % other

context(context: Context) public operator fun Expr<BitVecSort>.plus(other: Expr<BitVecSort>): BitVecExpr = context.mkBVAdd(this, other)
context(context: Context) public operator fun Expr<BitVecSort>.minus(other: Expr<BitVecSort>): BitVecExpr = context.mkBVSub(this, other)
context(context: Context) public operator fun Expr<BitVecSort>.times(other: Expr<BitVecSort>): BitVecExpr = context.mkBVMul(this, other)
context(context: Context) public operator fun Expr<BitVecSort>.div(other: Expr<BitVecSort>): BitVecExpr = context.mkBVSDiv(this, other)
context(context: Context) public operator fun Expr<BitVecSort>.rem(other: Expr<BitVecSort>): BitVecExpr = context.mkBVSRem(this, other)

context(context: Context) public operator fun Expr<BitVecSort>.unaryMinus(): BitVecExpr = context.mkBVNeg(this)

context(context: Context) public operator fun Expr<BitVecSort>.plus(other: Int): BitVecExpr = this + context.mkBV(other, sort.size)
context(context: Context) public operator fun Expr<BitVecSort>.minus(other: Int): BitVecExpr = this - context.mkBV(other, sort.size)
context(context: Context) public operator fun Expr<BitVecSort>.times(other: Int): BitVecExpr = this * context.mkBV(other, sort.size)
context(context: Context) public operator fun Expr<BitVecSort>.div(other: Int): BitVecExpr = this / context.mkBV(other, sort.size)
context(context: Context) public operator fun Expr<BitVecSort>.rem(other: Int): BitVecExpr = this % context.mkBV(other, sort.size)

context(context: Context) public operator fun Expr<BitVecSort>.plus(other: Long): BitVecExpr = this + context.mkBV(other, sort.size)
context(context: Context) public operator fun Expr<BitVecSort>.minus(other: Long): BitVecExpr = this - context.mkBV(other, sort.size)
context(context: Context) public operator fun Expr<BitVecSort>.times(other: Long): BitVecExpr = this * context.mkBV(other, sort.size)
context(context: Context) public operator fun Expr<BitVecSort>.div(other: Long): BitVecExpr = this / context.mkBV(other, sort.size)
context(context: Context) public operator fun Expr<BitVecSort>.rem(other: Long): BitVecExpr = this % context.mkBV(other, sort.size)

context(context: Context) public operator fun Int.plus(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) + other
context(context: Context) public operator fun Int.minus(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) - other
context(context: Context) public operator fun Int.times(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) * other
context(context: Context) public operator fun Int.div(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) / other
context(context: Context) public operator fun Int.rem(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) % other

context(context: Context) public operator fun Long.plus(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) + other
context(context: Context) public operator fun Long.minus(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) - other
context(context: Context) public operator fun Long.times(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) * other
context(context: Context) public operator fun Long.div(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) / other
context(context: Context) public operator fun Long.rem(other: Expr<BitVecSort>): BitVecExpr = context.mkBV(this, other.sort.size) % other

@JvmName("plusReal") context(context: Context) public operator fun Expr<RealSort>.plus(other: Int): ArithExpr<RealSort> = this + context.mkReal(other)
@JvmName("minusReal") context(context: Context) public operator fun Expr<RealSort>.minus(other: Int): ArithExpr<RealSort> = this - context.mkReal(other)
@JvmName("timesReal") context(context: Context) public operator fun Expr<RealSort>.times(other: Int): ArithExpr<RealSort> = this * context.mkReal(other)
@JvmName("divReal") context(context: Context) public operator fun Expr<RealSort>.div(other: Int): ArithExpr<RealSort> = this / context.mkReal(other)

@JvmName("plusReal") context(context: Context) public operator fun Expr<RealSort>.plus(other: Long): ArithExpr<RealSort> = this + context.mkReal(other)
@JvmName("minusReal") context(context: Context) public operator fun Expr<RealSort>.minus(other: Long): ArithExpr<RealSort> = this - context.mkReal(other)
@JvmName("timesReal") context(context: Context) public operator fun Expr<RealSort>.times(other: Long): ArithExpr<RealSort> = this * context.mkReal(other)
@JvmName("divReal") context(context: Context) public operator fun Expr<RealSort>.div(other: Long): ArithExpr<RealSort> = this / context.mkReal(other)

@JvmName("plusReal") context(context: Context) public operator fun Int.plus(other: Expr<RealSort>): ArithExpr<RealSort> = context.mkReal(this) + other
@JvmName("minusReal") context(context: Context) public operator fun Int.minus(other: Expr<RealSort>): ArithExpr<RealSort> = context.mkReal(this) - other
@JvmName("timesReal") context(context: Context) public operator fun Int.times(other: Expr<RealSort>): ArithExpr<RealSort> = context.mkReal(this) * other
@JvmName("divReal") context(context: Context) public operator fun Int.div(other: Expr<RealSort>): ArithExpr<RealSort> = context.mkReal(this) / other

@JvmName("plusReal") context(context: Context) public operator fun Long.plus(other: Expr<RealSort>): ArithExpr<RealSort> = context.mkReal(this) + other
@JvmName("minusReal") context(context: Context) public operator fun Long.minus(other: Expr<RealSort>): ArithExpr<RealSort> = context.mkReal(this) - other
@JvmName("timesReal") context(context: Context) public operator fun Long.times(other: Expr<RealSort>): ArithExpr<RealSort> = context.mkReal(this) * other
@JvmName("divReal") context(context: Context) public operator fun Long.div(other: Expr<RealSort>): ArithExpr<RealSort> = context.mkReal(this) / other

context(context: Context) public operator fun BoolExpr.not(): BoolExpr = context.mkNot(this)
//endregion

//region: Non-operator-fun math operations
context(context: Context) public infix fun Expr<IntSort>.mod(other: Expr<IntSort>): IntExpr = context.mkMod(this, other)
context(context: Context) public infix fun Expr<IntSort>.mod(other: Int): IntExpr = context.mkMod(this, context.mkInt(other))
context(context: Context) public infix fun Expr<IntSort>.mod(other: Long): IntExpr = context.mkMod(this, context.mkInt(other))
context(context: Context) public infix fun Int.mod(other: Expr<IntSort>): IntExpr = context.mkMod(context.mkInt(this), other)
context(context: Context) public infix fun Long.mod(other: Expr<IntSort>): IntExpr = context.mkMod(context.mkInt(this), other)

context(context: Context) public infix fun <T : ArithSort> Expr<T>.pow(other: Expr<T>): ArithExpr<T> = context.mkPower(this, other)
context(context: Context) public infix fun Expr<IntSort>.pow(other: Int): ArithExpr<IntSort> = context.mkPower(this, context.mkInt(other))
context(context: Context) public infix fun Expr<IntSort>.pow(other: Long): ArithExpr<IntSort> = context.mkPower(this, context.mkInt(other))
context(context: Context) public infix fun Int.pow(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkPower(context.mkInt(this), other)
context(context: Context) public infix fun Long.pow(other: Expr<IntSort>): ArithExpr<IntSort> = context.mkPower(context.mkInt(this), other)

context(context: Context) public infix fun Expr<BitVecSort>.mod(other: Expr<BitVecSort>): BitVecExpr = context.mkBVSMod(this, other)
context(context: Context) public infix fun Expr<BitVecSort>.mod(other: Int): BitVecExpr = context.mkBVSMod(this, context.mkBV(other, sort.size))
context(context: Context) public infix fun Expr<BitVecSort>.mod(other: Long): BitVecExpr = context.mkBVSMod(this, context.mkBV(other, sort.size))
context(context: Context) public infix fun Int.mod(other: Expr<BitVecSort>): BitVecExpr = context.mkBVSMod(context.mkBV(this, other.sort.size), other)
context(context: Context) public infix fun Long.mod(other: Expr<BitVecSort>): BitVecExpr = context.mkBVSMod(context.mkBV(this, other.sort.size), other)
//endregion

//region: Extra
public class IfThen<T : Sort> internal constructor(internal val condition: BoolExpr, internal val then: Expr<T>)
public infix fun <T : Sort> BoolExpr.ifTrue(then: Expr<T>): IfThen<T> = IfThen(this, then)
context(context: Context) public infix fun <T : Sort> IfThen<T>.ifFalse(otherwise: Expr<T>): Expr<T> = context.mkITE(condition, then, otherwise)
//@JvmName("ternaryIf") public infix fun <T : Sort> BoolExpr.`?`(then: Expr<T>): IfThen<T> = ifTrue(then)
//@JvmName("ternaryElse") @Suppress("INVALID_CHARACTERS") context(context: Context) public infix fun <T : Sort> IfThen<T>.`:`(otherwise: Expr<T>): Expr<T> = ifFalse(otherwise)
context(context: Context) public fun Expr<IntSort>.abs(): Expr<IntSort> = context.mkITE(this gte 0, this, -this)
context(context: Context) public fun Expr<IntSort>.sign(): Expr<IntSort> = context.mkITE(this eq 0, 0.toZ3Int(), context.mkITE(this gte 0, 1.toZ3Int(), (-1).toZ3Int()))
@JvmName("absReal") context(context: Context) public fun Expr<RealSort>.abs(): Expr<RealSort> = context.mkITE(this gte 0, this, this * context.mkReal(-1))
@JvmName("signReal") context(context: Context) public fun Expr<RealSort>.sign(): Expr<RealSort> = context.mkITE(this eq 0, context.mkReal(0), context.mkITE(this gte 0, context.mkReal(1), context.mkReal(-1)))
@JvmName("absBV") context(context: Context) public fun Expr<BitVecSort>.abs(): Expr<BitVecSort> = context.mkITE(this gte 0, this, -this)
@JvmName("signBV") context(context: Context) public fun Expr<BitVecSort>.sign(): Expr<BitVecSort> = context.mkITE(this eq 0, 0.toBitVec(sort.size), context.mkITE(this gte 0, 1.toBitVec(sort.size), (-1).toBitVec(sort.size)))

context(_: Context) public inline val Expr<IntSort>.absoluteValue: Expr<IntSort> get() = abs()
context(_: Context) public inline val Expr<IntSort>.sign: Expr<IntSort> get() = sign()
context(_: Context) public inline val Expr<RealSort>.absoluteValue: Expr<RealSort> @JvmName("get_absReal") get() = abs()
context(_: Context) public inline val Expr<RealSort>.sign: Expr<RealSort> @JvmName("get_signReal") get() = sign()
context(_: Context) public inline val Expr<BitVecSort>.absoluteValue: Expr<BitVecSort> @JvmName("get_absBV") get() = abs()
context(_: Context) public inline val Expr<BitVecSort>.sign: Expr<BitVecSort> @JvmName("get_signBV") get() = sign()
//endregion
