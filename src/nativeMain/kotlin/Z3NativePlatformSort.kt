package com.sschr15.z3kt

import kotlinx.cinterop.toKString
import lib.z3.*

context(ctx: Context)
internal fun Sort(native: Z3_sort): Sort = Sort(native, ctx)

internal fun Sort(native: Z3_sort, context: Context): Sort = when (Z3_get_sort_kind(context.native, native)) {
    Z3_ARRAY_SORT -> ArraySort<Sort, Sort>(native, context)
    Z3_BOOL_SORT -> BoolSort(native, context)
    Z3_BV_SORT -> BitVecSort(native, context)
    Z3_DATATYPE_SORT -> DatatypeSort<Sort>(native, context)
    Z3_INT_SORT -> IntSort(native, context)
    Z3_REAL_SORT -> RealSort(native, context)
    Z3_UNINTERPRETED_SORT -> UninterpretedSort(native, context)
    Z3_FINITE_DOMAIN_SORT -> FiniteDomainSort<Sort>(native, context)
    Z3_RELATION_SORT -> RelationSort(native, context)
    Z3_FLOATING_POINT_SORT -> FPSort(native, context)
    Z3_ROUNDING_MODE_SORT -> FPRMSort(native, context)
    Z3_SEQ_SORT -> SeqSort<Sort>(native, context)
    Z3_RE_SORT -> ReSort<Sort>(native, context)
    else -> throw Z3Exception("Unknown sort kind: ${Z3_get_sort_kind(context.native, native)}")
}

public actual open class Sort(context: Context, internal val native: Z3_sort) : AST(context, Z3_sort_to_ast(context.native, native)!!) {
    public actual override fun translate(otherContext: Context): Sort = super.translate(otherContext) as Sort
}

public actual open class ArithSort(native: Z3_sort, context: Context) : Sort(context, native)
public actual open class ArraySort<D : Sort, R : Sort>(native: Z3_sort, context: Context) : Sort(context, native)
public actual class BoolSort(native: Z3_sort, context: Context) : Sort(context, native)
public actual class IntSort(native: Z3_sort, context: Context) : ArithSort(native, context)
public actual class RealSort(native: Z3_sort, context: Context) : ArithSort(native, context)

public actual class BitVecSort(native: Z3_sort, context: Context) : Sort(context, native) {
    public actual fun getSize(): Int = Z3_get_bv_sort_size(context.native, native).toInt()
}

public actual class CharSort(native: Z3_sort, context: Context) : Sort(context, native)
public actual class SetSort<D : Sort>(native: Z3_sort, context: Context) : ArraySort<D, BoolSort>(native, context)
public actual class SeqSort<R : Sort>(native: Z3_sort, context: Context) : Sort(context, native)
public actual class ReSort<R : Sort>(native: Z3_sort, context: Context) : Sort(context, native)
public actual class DatatypeSort<R>(native: Z3_sort, context: Context) : Sort(context, native)
public actual class UninterpretedSort(native: Z3_sort, context: Context) : Sort(context, native)
public actual class TupleSort(native: Z3_sort, context: Context) : Sort(context, native)
public actual class ListSort<R : Sort>(native: Z3_sort, context: Context) : Sort(context, native)
public actual class EnumSort<R>(native: Z3_sort, context: Context) : Sort(context, native)
public actual class FiniteDomainSort<R>(native: Z3_sort, context: Context) : Sort(context, native)
public actual class FPSort(native: Z3_sort, context: Context) : Sort(context, native)
public actual class FPRMSort(native: Z3_sort, context: Context) : Sort(context, native)
public actual class RelationSort(native: Z3_sort, context: Context) : Sort(context, native)

context(ctx: Context) internal fun <D : Sort, R : Sort> ArraySort(native: Z3_sort): ArraySort<D, R> = ArraySort(native, ctx)
context(ctx: Context) internal fun BoolSort(native: Z3_sort): BoolSort = BoolSort(native, ctx)
context(ctx: Context) internal fun IntSort(native: Z3_sort): IntSort = IntSort(native, ctx)
context(ctx: Context) internal fun RealSort(native: Z3_sort): RealSort = RealSort(native, ctx)
context(ctx: Context) internal fun BitVecSort(native: Z3_sort): BitVecSort = BitVecSort(native, ctx)
context(ctx: Context) internal fun CharSort(native: Z3_sort): CharSort = CharSort(native, ctx)
context(ctx: Context) internal fun <D : Sort> SetSort(native: Z3_sort): SetSort<D> = SetSort(native, ctx)
context(ctx: Context) internal fun <R : Sort> SeqSort(native: Z3_sort): SeqSort<R> = SeqSort(native, ctx)
context(ctx: Context) internal fun <R : Sort> ReSort(native: Z3_sort): ReSort<R> = ReSort(native, ctx)
context(ctx: Context) internal fun <R> DatatypeSort(native: Z3_sort): DatatypeSort<R> = DatatypeSort(native, ctx)
context(ctx: Context) internal fun UninterpretedSort(native: Z3_sort): UninterpretedSort = UninterpretedSort(native, ctx)
context(ctx: Context) internal fun TupleSort(native: Z3_sort): TupleSort = TupleSort(native, ctx)
context(ctx: Context) internal fun <R : Sort> ListSort(native: Z3_sort): ListSort<R> = ListSort(native, ctx)
context(ctx: Context) internal fun <R> EnumSort(native: Z3_sort): EnumSort<R> = EnumSort(native, ctx)
context(ctx: Context) internal fun <R> FiniteDomainSort(native: Z3_sort): FiniteDomainSort<R> = FiniteDomainSort(native, ctx)
context(ctx: Context) internal fun FPSort(native: Z3_sort): FPSort = FPSort(native, ctx)
context(ctx: Context) internal fun FPRMSort(native: Z3_sort): FPRMSort = FPRMSort(native, ctx)
context(ctx: Context) internal fun RelationSort(native: Z3_sort): RelationSort = RelationSort(native, ctx)
