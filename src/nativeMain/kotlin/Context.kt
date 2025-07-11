package com.sschr15.z3kt

import kotlinx.cinterop.staticCFunction
import kotlinx.cinterop.toCValues
import kotlinx.cinterop.toKString
import lib.z3.*

internal val Array<*>?.size get() = this?.size ?: 0
internal val Array<out Sort>.native get() = map { it.native }.toCValues()
internal val Array<out Symbol>.native get() = map { it.native }.toCValues()
internal val Array<out Pattern>.native get() = map { it.native }.toCValues()
internal val Array<out FuncDecl<*>>.native get() = map { it.native }.toCValues()
internal val Array<out Tactic>.native get() = map { it.native }.toCValues()
internal val <T> Array<Constructor<T>>.native get() = map { it.native }.toCValues()
internal val Array<out Expr<*>>.native get() = map { it.native }.toCValues()

private fun errorHandler(context: Z3_context?, errorCode: Z3_error_code) {
    throw Z3Exception(Z3_get_error_msg(context, errorCode)!!.toKString())
}

public actual class Context public actual constructor(config: Map<String, String>) : AutoCloseable {
    private val boolSort by lazy(::mkBoolSort)
    private val intSort by lazy(::mkIntSort)
    private val realSort by lazy(::mkRealSort)
    private val stringSort by lazy(::mkStringSort)

    private var context: Z3_context? = if (config.isEmpty()) Z3_mk_context(null)!! else {
        val cfg = Z3_mk_config()!!
        for ((k, v) in config) {
            Z3_set_param_value(cfg, k, v)
        }
        val ctx = Z3_mk_context_rc(cfg)!!
        Z3_del_config(cfg)
        ctx
    }

    internal val native get() = context ?: throw IllegalStateException("Context has been disposed")

    public actual constructor() : this(emptyMap())

    init {
        setPrintMode(AstPrintMode.Z3_PRINT_SMTLIB2_COMPLIANT)
        Z3_set_error_handler_b(context, staticCFunction(::errorHandler))
    }

    public actual fun mkSymbol(id: Int): IntSymbol = IntSymbol(Z3_mk_int_symbol(context, id)!!, this)
    public actual fun mkSymbol(name: String): StringSymbol = StringSymbol(Z3_mk_string_symbol(context, name)!!, this)
    public actual fun getBoolSort(): BoolSort = boolSort
    public actual fun getIntSort(): IntSort = intSort
    public actual fun getRealSort(): RealSort = realSort
    public actual fun mkBoolSort(): BoolSort = BoolSort(Z3_mk_bool_sort(context)!!)
    public actual fun mkCharSort(): CharSort = CharSort(Z3_mk_char_sort(context)!!)
    public actual fun getStringSort(): SeqSort<CharSort> = stringSort
    public actual fun mkUninterpretedSort(s: Symbol): UninterpretedSort = UninterpretedSort(Z3_mk_uninterpreted_sort(context, s.native)!!)
    public actual fun mkUninterpretedSort(name: String): UninterpretedSort = mkUninterpretedSort(mkSymbol(name))
    public actual fun mkIntSort(): IntSort = IntSort(Z3_mk_int_sort(context)!!)
    public actual fun mkRealSort(): RealSort = RealSort(Z3_mk_real_sort(context)!!)
    public actual fun mkBitVecSort(size: Int): BitVecSort = BitVecSort(Z3_mk_bv_sort(context, size.toUInt())!!)

    public actual fun <D : Sort, R : Sort> mkArraySort(domain: D, range: R): ArraySort<D, R> =
        ArraySort(Z3_mk_array_sort(context, domain.native, range.native)!!)

    public actual fun <R : Sort> mkArraySort(domain: Array<Sort>, range: R): ArraySort<Sort, R> =
        ArraySort(Z3_mk_array_sort_n(context, domain.size.toUInt(), domain.native, range.native)!!)

    public actual fun mkStringSort(): SeqSort<CharSort> = SeqSort(Z3_mk_string_sort(context)!!)
    public actual fun <R : Sort> mkSeqSort(elementSort: R): SeqSort<R> = SeqSort(Z3_mk_seq_sort(context, elementSort.native)!!)
    public actual fun <R : Sort> mkReSort(elementSort: R): ReSort<R> = ReSort(Z3_mk_re_sort(context, elementSort.native)!!)

    public actual fun mkTupleSort(name: Symbol, fieldNames: Array<Symbol>, fieldSorts: Array<Sort>): TupleSort =
        TupleSort(Z3_mk_tuple_sort(context, name.native, fieldNames.size.toUInt(), fieldNames.native, fieldSorts.native, null, null)!!)

    public actual fun <R> mkEnumSort(name: Symbol, vararg enumNames: Symbol): EnumSort<R> =
        EnumSort(Z3_mk_enumeration_sort(context, name.native, enumNames.size.toUInt(), enumNames.map { it.native }.toCValues(), null, null)!!)

    public actual fun <R> mkEnumSort(name: String, vararg enumNames: String): EnumSort<R> =
        mkEnumSort(mkSymbol(name), *enumNames.map { mkSymbol(it) }.toTypedArray())

    public actual fun <R : Sort> mkListSort(name: Symbol, elementSort: R): ListSort<R> =
        ListSort(Z3_mk_list_sort(context, name.native, elementSort.native, null, null, null, null, null, null)!!)

    public actual fun <R : Sort> mkListSort(name: String, elementSort: R): ListSort<R> =
        mkListSort(mkSymbol(name), elementSort)

    public actual fun <R> mkFiniteDomainSort(name: Symbol, size: Long): FiniteDomainSort<R> =
        FiniteDomainSort(Z3_mk_finite_domain_sort(context, name.native, size.toULong())!!)

    public actual fun <R> mkFiniteDomainSort(name: String, size: Long): FiniteDomainSort<R> =
        mkFiniteDomainSort(mkSymbol(name), size)

    public actual fun <R> mkConstructor(
        name: Symbol,
        recognizer: Symbol,
        fieldNames: Array<Symbol>,
        sorts: Array<Sort>,
        sortRefs: IntArray
    ): Constructor<R> {
        check(sorts.size == fieldNames.size) { "sorts.size != fieldNames.size" }
        check(sortRefs.size == sorts.size) { "sortRefs.size != sorts.size" }
        return Constructor(Z3_mk_constructor(context, name.native, recognizer.native, sorts.size.toUInt(), fieldNames.native, sorts.native, sortRefs.toUIntArray().toCValues())!!, this)
    }

    public actual fun <R> mkConstructor(name: String, recognizer: String, fieldNames: Array<String>, sorts: Array<Sort>, sortRefs: IntArray): Constructor<R> =
        mkConstructor(mkSymbol(name), mkSymbol(recognizer), fieldNames.map(::mkSymbol).toTypedArray(), sorts, sortRefs)

    public actual fun <R> mkDatatypeSort(name: Symbol, constructors: Array<Constructor<R>>): DatatypeSort<R> =
        DatatypeSort(Z3_mk_datatype(context, name.native, constructors.size.toUInt(), constructors.native)!!)

    public actual fun <R> mkDatatypeSort(name: String, constructors: Array<Constructor<R>>): DatatypeSort<R> =
        mkDatatypeSort(mkSymbol(name), constructors)

    public actual fun mkDatatypeSorts(
        names: Array<Symbol>,
        constructors: Array<Array<Constructor<Any>>>
    ): Array<DatatypeSort<Any>> {
        val results = arrayOfNulls<Z3_sort>(names.size)
        val ctors = constructors.map { Z3_mk_constructor_list(context, it.size.toUInt(), it.native) }.toCValues()
        Z3_mk_datatypes(context, names.size.toUInt(), names.native, results.toCValues(), ctors)
        return results.map { DatatypeSort<Any>(it!!) }.toTypedArray()
    }

    public actual fun mkDatatypeSorts(names: Array<String>, constructors: Array<Array<Constructor<Any>>>): Array<DatatypeSort<Any>> = mkDatatypeSorts(names.map(::mkSymbol).toTypedArray(), constructors)

    public actual fun <F : Sort, R : Sort> mkUpdateField(accessor: FuncDecl<F>, value: Expr<R>, field: Expr<F>): Expr<R> =
        Expr(Z3_datatype_update_field(context, accessor.native, value.native, field.native)!!)

    public actual fun <R : Sort> mkFuncDecl(name: Symbol, domain: Array<Sort>, range: R): FuncDecl<R> =
        FuncDecl(Z3_mk_func_decl(context, name.native, domain.size.toUInt(), domain.native, range.native)!!)

    public actual fun <R : Sort> mkFuncDecl(name: Symbol, domain: Sort, range: R): FuncDecl<R> =
        mkFuncDecl(name, arrayOf(domain), range)

    public actual fun <R : Sort> mkFuncDecl(name: String, domain: Array<Sort>, range: R): FuncDecl<R> =
        mkFuncDecl(mkSymbol(name), domain, range)

    public actual fun <R : Sort> mkFuncDecl(name: String, domain: Sort, range: R): FuncDecl<R> =
        mkFuncDecl(mkSymbol(name), arrayOf(domain), range)

    public actual fun <R : Sort> mkPropagateFunction(name: Symbol, domain: Array<Sort>, range: R): FuncDecl<R> =
        FuncDecl(Z3_solver_propagate_declare(context, name.native, domain.size.toUInt(), domain.native, range.native)!!)

    public actual fun <R : Sort> mkRecFuncDecl(name: Symbol, domain: Array<Sort>, range: R): FuncDecl<R> =
        FuncDecl(Z3_mk_rec_func_decl(context, name.native, domain.size.toUInt(), domain.native, range.native)!!)

    public actual fun <R : Sort> AddRecDef(f: FuncDecl<R>, args: Array<Expr<*>>, body: Expr<R>) {
        Z3_add_rec_def(context, f.native, args.size.toUInt(), args.native, body.native)
    }

    public actual fun <R : Sort> mkFreshFuncDecl(prefix: String, domain: Array<Sort>, range: R): FuncDecl<R> =
        FuncDecl(Z3_mk_fresh_func_decl(context, prefix, domain.size.toUInt(), domain.native, range.native)!!)

    public actual fun <R : Sort> mkConstDecl(name: Symbol, sort: R): FuncDecl<R> =
        FuncDecl(Z3_mk_func_decl(context, name.native, 0.toUInt(), null, sort.native)!!)

    public actual fun <R : Sort> mkConstDecl(name: String, sort: R): FuncDecl<R> =
        mkConstDecl(mkSymbol(name), sort)

    public actual fun <R : Sort> mkFreshConstDecl(prefix: String, sort: R): FuncDecl<R> =
        FuncDecl(Z3_mk_fresh_func_decl(context, prefix, 0.toUInt(), null, sort.native)!!)

    public actual fun <R : Sort> mkBound(index: Int, sort: R): Expr<R> = Expr(
        Z3_mk_bound(
            context,
            index.toUInt(),
            sort.native,
        )!!,
    )
    public actual fun mkPattern(vararg terms: Expr<*>): Pattern = Pattern(Z3_mk_pattern(context, terms.size.toUInt(), terms.native)!!, this)
    public actual fun <R : Sort> mkConst(s: Symbol, sort: R): Expr<R> = Expr(Z3_mk_const(context, s.native, sort.native)!!)
    public actual fun <R : Sort> mkConst(name: String, sort: R): Expr<R> = mkConst(mkSymbol(name), sort)
    public actual fun <R : Sort> mkConst(decl: FuncDecl<R>): Expr<R> = mkApp(decl)
    public actual fun <R : Sort> mkFreshConst(prefix: String, sort: R): Expr<R> = Expr(
        Z3_mk_fresh_const(
            context,
            prefix,
            sort.native,
        )!!,
    )
    public actual fun mkBoolConst(s: Symbol): BoolExpr = BoolExpr(Z3_mk_const(context, s.native, boolSort.native)!!)
    public actual fun mkBoolConst(name: String): BoolExpr = mkBoolConst(mkSymbol(name))
    public actual fun mkIntConst(s: Symbol): IntExpr = IntExpr(Z3_mk_const(context, s.native, intSort.native)!!)
    public actual fun mkIntConst(name: String): IntExpr = mkIntConst(mkSymbol(name))
    public actual fun mkRealConst(s: Symbol): RealExpr = RealExpr(Z3_mk_const(context, s.native, realSort.native)!!)
    public actual fun mkRealConst(name: String): RealExpr = mkRealConst(mkSymbol(name))
    public actual fun mkBVConst(s: Symbol, size: Int): BitVecExpr = BitVecExpr(Z3_mk_const(context, s.native, Z3_mk_bv_sort(context, size.toUInt()))!!)
    public actual fun mkBVConst(name: String, size: Int): BitVecExpr = mkBVConst(mkSymbol(name), size)

    public actual fun <R : Sort> mkApp(f: FuncDecl<R>, vararg args: Expr<*>): Expr<R> =
        Expr(Z3_mk_app(context, f.native, args.size.toUInt(), args.native)!!)

    public actual fun mkTrue(): BoolExpr = BoolExpr(Z3_mk_true(context)!!)
    public actual fun mkFalse(): BoolExpr = BoolExpr(Z3_mk_false(context)!!)
    public actual fun mkBool(value: Boolean): BoolExpr = if (value) mkTrue() else mkFalse()

    public actual fun mkEq(left: Expr<*>, right: Expr<*>): BoolExpr = BoolExpr(Z3_mk_eq(context, left.native, right.native)!!)
    public actual fun mkDistinct(vararg args: Expr<*>): BoolExpr = BoolExpr(Z3_mk_distinct(context, args.size.toUInt(), args.native)!!)
    public actual fun mkNot(expr: Expr<BoolSort>): BoolExpr = BoolExpr(Z3_mk_not(context, expr.native)!!)

    public actual fun <R : Sort> mkITE(condition: Expr<BoolSort>, thenExpr: Expr<out R>, elseExpr: Expr<out R>): Expr<R> =
        Expr(Z3_mk_ite(context, condition.native, thenExpr.native, elseExpr.native)!!)

    public actual fun mkIff(left: Expr<BoolSort>, right: Expr<BoolSort>): BoolExpr = BoolExpr(Z3_mk_iff(context, left.native, right.native)!!)
    public actual fun mkImplies(left: Expr<BoolSort>, right: Expr<BoolSort>): BoolExpr = BoolExpr(Z3_mk_implies(context, left.native, right.native)!!)
    public actual fun mkXor(left: Expr<BoolSort>, right: Expr<BoolSort>): BoolExpr = BoolExpr(Z3_mk_xor(context, left.native, right.native)!!)
    public actual fun mkAnd(vararg args: Expr<BoolSort>): BoolExpr = BoolExpr(Z3_mk_and(context, args.size.toUInt(), args.native)!!)
    public actual fun mkOr(vararg args: Expr<BoolSort>): BoolExpr = BoolExpr(Z3_mk_or(context, args.size.toUInt(), args.native)!!)
    public actual fun <R : ArithSort> mkAdd(vararg args: Expr<out R>): ArithExpr<R> = ArithExpr(Z3_mk_add(context, args.size.toUInt(), args.native)!!, this)
    public actual fun <R : ArithSort> mkMul(vararg args: Expr<out R>): ArithExpr<R> = ArithExpr(Z3_mk_mul(context, args.size.toUInt(), args.native)!!, this)
    public actual fun <R : ArithSort> mkSub(vararg args: Expr<out R>): ArithExpr<R> = ArithExpr(Z3_mk_sub(context, args.size.toUInt(), args.native)!!, this)
    public actual fun <R : ArithSort> mkUnaryMinus(expr: Expr<R>): ArithExpr<R> = ArithExpr(Z3_mk_unary_minus(context, expr.native)!!, this)
    public actual fun <R : ArithSort> mkDiv(numerator: Expr<out R>, denominator: Expr<out R>): ArithExpr<R> = ArithExpr(Z3_mk_div(context, numerator.native, denominator.native)!!, this)
    public actual fun mkMod(left: Expr<IntSort>, right: Expr<IntSort>): IntExpr = IntExpr(Z3_mk_mod(context, left.native, right.native)!!)
    public actual fun mkRem(left: Expr<IntSort>, right: Expr<IntSort>): IntExpr = IntExpr(Z3_mk_rem(context, left.native, right.native)!!)
    public actual fun <R : ArithSort> mkPower(base: Expr<out R>, exponent: Expr<out R>): ArithExpr<R> = ArithExpr(Z3_mk_power(context, base.native, exponent.native)!!, this)
    public actual fun <R : Sort> mkPower(regex: Expr<ReSort<R>>, count: Int): ReExpr<R> = ReExpr(Z3_mk_re_power(context, regex.native, count.toUInt())!!)
    public actual fun mkLt(left: Expr<out ArithSort>, right: Expr<out ArithSort>): BoolExpr = BoolExpr(Z3_mk_lt(context, left.native, right.native)!!)
    public actual fun mkLe(left: Expr<out ArithSort>, right: Expr<out ArithSort>): BoolExpr = BoolExpr(Z3_mk_le(context, left.native, right.native)!!)
    public actual fun mkGt(left: Expr<out ArithSort>, right: Expr<out ArithSort>): BoolExpr = BoolExpr(Z3_mk_gt(context, left.native, right.native)!!)
    public actual fun mkGe(left: Expr<out ArithSort>, right: Expr<out ArithSort>): BoolExpr = BoolExpr(Z3_mk_ge(context, left.native, right.native)!!)
    public actual fun mkInt2Real(expr: Expr<IntSort>): RealExpr = RealExpr(Z3_mk_int2real(context, expr.native)!!)
    public actual fun mkReal2Int(expr: Expr<RealSort>): IntExpr = IntExpr(Z3_mk_real2int(context, expr.native)!!)
    public actual fun mkIsInteger(expr: Expr<RealSort>): BoolExpr = BoolExpr(Z3_mk_is_int(context, expr.native)!!)
    public actual fun mkBVNot(expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvnot(context, expr.native)!!)
    public actual fun mkBVRedAND(expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvredand(context, expr.native)!!)
    public actual fun mkBVRedOR(expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvredor(context, expr.native)!!)
    public actual fun mkBVAND(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvand(context, left.native, right.native)!!)
    public actual fun mkBVOR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvor(context, left.native, right.native)!!)
    public actual fun mkBVXOR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvxor(context, left.native, right.native)!!)
    public actual fun mkBVNAND(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvnand(context, left.native, right.native)!!)
    public actual fun mkBVNOR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvnor(context, left.native, right.native)!!)
    public actual fun mkBVXNOR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvxnor(context, left.native, right.native)!!)
    public actual fun mkBVNeg(expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvneg(context, expr.native)!!)
    public actual fun mkBVAdd(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvadd(context, left.native, right.native)!!)
    public actual fun mkBVSub(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvsub(context, left.native, right.native)!!)
    public actual fun mkBVMul(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvmul(context, left.native, right.native)!!)
    public actual fun mkBVUDiv(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvudiv(context, left.native, right.native)!!)
    public actual fun mkBVSDiv(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvsdiv(context, left.native, right.native)!!)
    public actual fun mkBVURem(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvurem(context, left.native, right.native)!!)
    public actual fun mkBVSRem(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvsrem(context, left.native, right.native)!!)
    public actual fun mkBVSMod(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvsmod(context, left.native, right.native)!!)
    public actual fun mkBVULT(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr = BoolExpr(Z3_mk_bvult(context, left.native, right.native)!!)
    public actual fun mkBVSLT(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr = BoolExpr(Z3_mk_bvslt(context, left.native, right.native)!!)
    public actual fun mkBVULE(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr = BoolExpr(Z3_mk_bvule(context, left.native, right.native)!!)
    public actual fun mkBVSLE(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr = BoolExpr(Z3_mk_bvsle(context, left.native, right.native)!!)
    public actual fun mkBVUGE(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr = BoolExpr(Z3_mk_bvuge(context, left.native, right.native)!!)
    public actual fun mkBVSGE(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr = BoolExpr(Z3_mk_bvsge(context, left.native, right.native)!!)
    public actual fun mkBVUGT(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr = BoolExpr(Z3_mk_bvugt(context, left.native, right.native)!!)
    public actual fun mkBVSGT(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr = BoolExpr(Z3_mk_bvsgt(context, left.native, right.native)!!)
    public actual fun mkConcat(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_concat(context, left.native, right.native)!!)
    public actual fun <R : Sort> mkConcat(vararg sequences: Expr<SeqSort<R>>): SeqExpr<R> = SeqExpr(Z3_mk_seq_concat(context, sequences.size.toUInt(), sequences.native)!!)
    public actual fun <R : Sort> mkConcat(vararg regexes: ReExpr<R>): ReExpr<R> = ReExpr(Z3_mk_re_concat(context, regexes.size.toUInt(), regexes.native)!!)
    public actual fun mkExtract(high: Int, low: Int, expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_extract(context, high.toUInt(), low.toUInt(), expr.native)!!)

    public actual fun <R : Sort> mkExtract(sequence: Expr<SeqSort<R>>, offset: Expr<IntSort>, length: Expr<IntSort>): SeqExpr<R> =
        SeqExpr(Z3_mk_seq_extract(context, offset.native, length.native, sequence.native)!!)

    public actual fun mkSignExt(count: Int, expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_sign_ext(context, count.toUInt(), expr.native)!!)
    public actual fun mkZeroExt(count: Int, expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_zero_ext(context, count.toUInt(), expr.native)!!)
    public actual fun mkRepeat(count: Int, expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_repeat(context, count.toUInt(), expr.native)!!)
    public actual fun mkBVSHL(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvshl(context, left.native, right.native)!!)
    public actual fun mkBVLSHR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvlshr(context, left.native, right.native)!!)
    public actual fun mkBVASHR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_bvashr(context, left.native, right.native)!!)
    public actual fun mkBVRotateLeft(count: Int, expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_rotate_left(context, count.toUInt(), expr.native)!!)
    public actual fun mkBVRotateLeft(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_ext_rotate_left(context, left.native, right.native)!!)
    public actual fun mkBVRotateRight(count: Int, expr: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_rotate_right(context, count.toUInt(), expr.native)!!)
    public actual fun mkBVRotateRight(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr = BitVecExpr(Z3_mk_ext_rotate_right(context, left.native, right.native)!!)
    public actual fun mkInt2BV(size: Int, expr: Expr<IntSort>): BitVecExpr = BitVecExpr(Z3_mk_int2bv(context, size.toUInt(), expr.native)!!)
    public actual fun mkBV2Int(expr: Expr<BitVecSort>, isSigned: Boolean): IntExpr = IntExpr(Z3_mk_bv2int(context, expr.native, isSigned)!!)

    public actual fun mkBVAddNoOverflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>, isSigned: Boolean): BoolExpr =
        BoolExpr(Z3_mk_bvadd_no_overflow(context, left.native, right.native, isSigned)!!)

    public actual fun mkBVAddNoUnderflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr =
        BoolExpr(Z3_mk_bvadd_no_underflow(context, left.native, right.native)!!)

    public actual fun mkBVSubNoOverflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr =
        BoolExpr(Z3_mk_bvsub_no_overflow(context, left.native, right.native)!!)

    public actual fun mkBVSubNoUnderflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>, isSigned: Boolean): BoolExpr =
        BoolExpr(Z3_mk_bvsub_no_underflow(context, left.native, right.native, isSigned)!!)

    public actual fun mkBVSDivNoOverflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr =
        BoolExpr(Z3_mk_bvsdiv_no_overflow(context, left.native, right.native)!!)

    public actual fun mkBVNegNoOverflow(expr: Expr<BitVecSort>): BoolExpr =
        BoolExpr(Z3_mk_bvneg_no_overflow(context, expr.native)!!)

    public actual fun mkBVMulNoOverflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>, isSigned: Boolean): BoolExpr =
        BoolExpr(Z3_mk_bvmul_no_overflow(context, left.native, right.native, isSigned)!!)

    public actual fun mkBVMulNoUnderflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr =
        BoolExpr(Z3_mk_bvmul_no_underflow(context, left.native, right.native)!!)

    public actual fun <D : Sort, R : Sort> mkArrayConst(name: Symbol, domain: D, range: R): ArrayExpr<D, R> =
        ArrayExpr(Z3_mk_const(context, name.native, Z3_mk_array_sort(context, domain.native, range.native))!!)

    public actual fun <D : Sort, R : Sort> mkArrayConst(name: String, domain: D, range: R): ArrayExpr<D, R> =
        mkArrayConst(mkSymbol(name), domain, range)

    public actual fun <D : Sort, R : Sort> mkSelect(array: Expr<ArraySort<D, R>>, index: Expr<D>): Expr<R> =
        Expr(Z3_mk_select(context, array.native, index.native)!!)

    public actual fun <R : Sort> mkSelect(array: Expr<ArraySort<Sort, R>>, indices: Array<Expr<*>>): Expr<R> =
        Expr(Z3_mk_select_n(context, array.native, indices.size.toUInt(), indices.native)!!)

    public actual fun <D : Sort, R : Sort> mkStore(array: Expr<ArraySort<D, R>>, index: Expr<D>, value: Expr<R>): ArrayExpr<D, R> =
        ArrayExpr(Z3_mk_store(context, array.native, index.native, value.native)!!)

    public actual fun <R : Sort> mkStore(array: Expr<ArraySort<Sort, R>>, indices: Array<Expr<*>>, value: Expr<R>): ArrayExpr<Sort, R> =
        ArrayExpr(Z3_mk_store_n(context, array.native, indices.size.toUInt(), indices.native, value.native)!!)

    public actual fun <D : Sort, R : Sort> mkConstArray(domain: D, value: Expr<R>): ArrayExpr<D, R> =
        ArrayExpr(Z3_mk_const_array(context, domain.native, value.native)!!)

    public actual fun <D : Sort, R1 : Sort, R2 : Sort> mkMap(f: FuncDecl<R2>, vararg arrays: Expr<ArraySort<D, R1>>): ArrayExpr<D, R2> =
        ArrayExpr(Z3_mk_map(context, f.native, arrays.size.toUInt(), arrays.native)!!)

    public actual fun <D : Sort, R : Sort> mkTermArray(array: Expr<ArraySort<D, R>>): Expr<R> =
        Expr(Z3_mk_array_default(context, array.native)!!)

    public actual fun <D : Sort, R : Sort> mkArrayExt(left: Expr<ArraySort<D, R>>, right: Expr<ArraySort<D, R>>): Expr<D> =
        Expr(Z3_mk_array_ext(context, left.native, right.native)!!)

    public actual fun <D : Sort> mkSetSort(elementSort: D): SetSort<D> =
        SetSort(Z3_mk_set_sort(context, elementSort.native)!!)

    public actual fun <D : Sort> mkEmptySet(elementSort: D): ArrayExpr<D, BoolSort> =
        ArrayExpr(Z3_mk_empty_set(context, elementSort.native)!!)

    public actual fun <D : Sort> mkFullSet(elementSort: D): ArrayExpr<D, BoolSort> =
        ArrayExpr(Z3_mk_full_set(context, elementSort.native)!!)

    public actual fun <D : Sort> mkSetAdd(set: Expr<ArraySort<D, BoolSort>>, element: Expr<D>): ArrayExpr<D, BoolSort> =
        ArrayExpr(Z3_mk_set_add(context, set.native, element.native)!!)

    public actual fun <D : Sort> mkSetDel(set: Expr<ArraySort<D, BoolSort>>, element: Expr<D>): ArrayExpr<D, BoolSort> =
        ArrayExpr(Z3_mk_set_del(context, set.native, element.native)!!)

    public actual fun <D : Sort> mkSetUnion(vararg sets: Expr<ArraySort<D, BoolSort>>): ArrayExpr<D, BoolSort> =
        ArrayExpr(Z3_mk_set_union(context, sets.size.toUInt(), sets.native)!!)

    public actual fun <D : Sort> mkSetIntersection(vararg sets: Expr<ArraySort<D, BoolSort>>): ArrayExpr<D, BoolSort> =
        ArrayExpr(Z3_mk_set_intersect(context, sets.size.toUInt(), sets.native)!!)

    public actual fun <D : Sort> mkSetDifference(left: Expr<ArraySort<D, BoolSort>>, right: Expr<ArraySort<D, BoolSort>>): ArrayExpr<D, BoolSort> =
        ArrayExpr(Z3_mk_set_difference(context, left.native, right.native)!!)

    public actual fun <D : Sort> mkSetComplement(set: Expr<ArraySort<D, BoolSort>>): ArrayExpr<D, BoolSort> =
        ArrayExpr(Z3_mk_set_complement(context, set.native)!!)

    public actual fun <D : Sort> mkSetMembership(element: Expr<D>, set: Expr<ArraySort<D, BoolSort>>): BoolExpr =
        BoolExpr(Z3_mk_set_member(context, element.native, set.native)!!)

    public actual fun <D : Sort> mkSetSubset(subset: Expr<ArraySort<D, BoolSort>>, superset: Expr<ArraySort<D, BoolSort>>): BoolExpr =
        BoolExpr(Z3_mk_set_subset(context, subset.native, superset.native)!!)

    public actual fun <R : Sort> mkEmptySeq(sort: R): SeqExpr<R> = SeqExpr(Z3_mk_seq_empty(context, sort.native)!!)
    public actual fun <R : Sort> mkUnit(expr: Expr<R>): SeqExpr<R> = SeqExpr(Z3_mk_seq_unit(context, expr.native)!!)
    public actual fun mkString(s: String): SeqExpr<CharSort> = SeqExpr(Z3_mk_string(context, s)!!)
    public actual fun intToString(expr: Expr<IntSort>): SeqExpr<CharSort> = SeqExpr(Z3_mk_int_to_str(context, expr.native)!!)
    public actual fun ubvToString(expr: Expr<BitVecSort>): SeqExpr<CharSort> = SeqExpr(Z3_mk_ubv_to_str(context, expr.native)!!)
    public actual fun sbvToString(expr: Expr<BitVecSort>): SeqExpr<CharSort> = SeqExpr(Z3_mk_sbv_to_str(context, expr.native)!!)
    public actual fun stringToInt(expr: Expr<SeqSort<CharSort>>): IntExpr = IntExpr(Z3_mk_str_to_int(context, expr.native)!!)
    public actual fun <R : Sort> mkLength(sequence: Expr<SeqSort<R>>): IntExpr = IntExpr(Z3_mk_seq_length(context, sequence.native)!!)

    public actual fun <R : Sort> mkPrefixOf(prefix: Expr<SeqSort<R>>, sequence: Expr<SeqSort<R>>): BoolExpr =
        BoolExpr(Z3_mk_seq_prefix(context, prefix.native, sequence.native)!!)

    public actual fun <R : Sort> mkSuffixOf(suffix: Expr<SeqSort<R>>, sequence: Expr<SeqSort<R>>): BoolExpr =
        BoolExpr(Z3_mk_seq_suffix(context, suffix.native, sequence.native)!!)

    public actual fun <R : Sort> mkContains(sequence: Expr<SeqSort<R>>, subsequence: Expr<SeqSort<R>>): BoolExpr =
        BoolExpr(Z3_mk_seq_contains(context, sequence.native, subsequence.native)!!)

    public actual fun MkStringLt(left: Expr<SeqSort<CharSort>>, right: Expr<SeqSort<CharSort>>): BoolExpr =
        BoolExpr(Z3_mk_str_lt(context, left.native, right.native)!!)

    public actual fun MkStringLe(left: Expr<SeqSort<CharSort>>, right: Expr<SeqSort<CharSort>>): BoolExpr =
        BoolExpr(Z3_mk_str_le(context, left.native, right.native)!!)

    public actual fun <R : Sort> mkAt(sequence: Expr<SeqSort<R>>, index: Expr<IntSort>): SeqExpr<R> =
        SeqExpr(Z3_mk_seq_at(context, sequence.native, index.native)!!)

    public actual fun <R : Sort> mkNth(sequence: Expr<SeqSort<R>>, index: Expr<IntSort>): Expr<R> =
        Expr(Z3_mk_seq_nth(context, sequence.native, index.native)!!)

    public actual fun <R : Sort> mkIndexOf(sequence: Expr<SeqSort<R>>, subsequence: Expr<SeqSort<R>>, offset: Expr<IntSort>): IntExpr =
        IntExpr(Z3_mk_seq_index(context, sequence.native, subsequence.native, offset.native)!!)

    public actual fun <R : Sort> mkReplace(sequence: Expr<SeqSort<R>>, src: Expr<SeqSort<R>>, dst: Expr<SeqSort<R>>): SeqExpr<R> =
        SeqExpr(Z3_mk_seq_replace(context, sequence.native, src.native, dst.native)!!)

    public actual fun <R : Sort> mkToRe(sequence: Expr<SeqSort<R>>): ReExpr<SeqSort<R>> =
        ReExpr(Z3_mk_seq_to_re(context, sequence.native)!!)

    public actual fun <R : Sort> mkInRe(sequence: Expr<SeqSort<R>>, regex: ReExpr<SeqSort<R>>): BoolExpr =
        BoolExpr(Z3_mk_seq_in_re(context, sequence.native, regex.native)!!)

    public actual fun <R : Sort> mkStar(regex: Expr<ReSort<R>>): ReExpr<R> =
        ReExpr(Z3_mk_re_star(context, regex.native)!!)

    public actual fun <R : Sort> mkLoop(regex: Expr<ReSort<R>>, min: Int, max: Int): ReExpr<R> =
        ReExpr(Z3_mk_re_loop(context, regex.native, min.toUInt(), max.toUInt())!!)

    public actual fun <R : Sort> mkLoop(regex: Expr<ReSort<R>>, count: Int): ReExpr<R> =
        ReExpr(Z3_mk_re_loop(context, regex.native, count.toUInt(), count.toUInt())!!)

    public actual fun <R : Sort> mkPlus(regex: Expr<ReSort<R>>): ReExpr<R> =
        ReExpr(Z3_mk_re_plus(context, regex.native)!!)

    public actual fun <R : Sort> mkOption(regex: Expr<ReSort<R>>): ReExpr<R> =
        ReExpr(Z3_mk_re_option(context, regex.native)!!)

    public actual fun <R : Sort> mkComplement(regex: Expr<ReSort<R>>): ReExpr<R> =
        ReExpr(Z3_mk_re_complement(context, regex.native)!!)

    public actual fun <R : Sort> mkUnion(vararg regexes: Expr<ReSort<R>>): ReExpr<R> =
        ReExpr(Z3_mk_re_union(context, regexes.size.toUInt(), regexes.native)!!)

    public actual fun <R : Sort> mkIntersect(vararg regexes: Expr<ReSort<R>>): ReExpr<R> =
        ReExpr(Z3_mk_re_intersect(context, regexes.size.toUInt(), regexes.native)!!)

    public actual fun <R : Sort> mkDiff(left: Expr<ReSort<R>>, right: Expr<ReSort<R>>): ReExpr<R> =
        ReExpr(Z3_mk_re_diff(context, left.native, right.native)!!)

    public actual fun <R : Sort> mkEmptyRe(sort: ReSort<R>): ReExpr<R> =
        ReExpr(Z3_mk_re_empty(context, sort.native)!!)

    public actual fun <R : Sort> mkFullRe(sort: ReSort<R>): ReExpr<R> =
        ReExpr(Z3_mk_re_full(context, sort.native)!!)

    public actual fun <R : Sort> mkAllcharRe(sort: ReSort<R>): ReExpr<R> =
        ReExpr(Z3_mk_re_allchar(context, sort.native)!!)

    public actual fun mkRange(from: Expr<SeqSort<CharSort>>, to: Expr<SeqSort<CharSort>>): ReExpr<SeqSort<CharSort>> =
        ReExpr(Z3_mk_re_range(context, from.native, to.native)!!)

    public actual fun mkCharLe(left: Expr<CharSort>, right: Expr<CharSort>): BoolExpr =
        BoolExpr(Z3_mk_char_le(context, left.native, right.native)!!)

    public actual fun charToInt(char: Expr<CharSort>): IntExpr =
        IntExpr(Z3_mk_char_to_int(context, char.native)!!)

    public actual fun charToBv(char: Expr<CharSort>): BitVecExpr =
        BitVecExpr(Z3_mk_char_to_bv(context, char.native)!!)

    public actual fun charFromBv(bv: BitVecExpr): Expr<CharSort> =
        Expr(Z3_mk_char_from_bv(context, bv.native)!!)

    public actual fun mkIsDigit(char: Expr<CharSort>): BoolExpr =
        BoolExpr(Z3_mk_char_is_digit(context, char.native)!!)

    public actual fun mkAtMost(literals: Array<Expr<BoolSort>>, k: Int): BoolExpr =
        BoolExpr(Z3_mk_atmost(context, literals.size.toUInt(), literals.native, k.toUInt())!!)

    public actual fun mkAtLeast(literals: Array<Expr<BoolSort>>, k: Int): BoolExpr =
        BoolExpr(Z3_mk_atleast(context, literals.size.toUInt(), literals.native, k.toUInt())!!)

    public actual fun mkPBLe(coefficients: IntArray, literals: Array<Expr<BoolSort>>, k: Int): BoolExpr =
        BoolExpr(Z3_mk_pble(context, literals.size.toUInt(), literals.native, coefficients.toCValues(), k)!!)

    public actual fun mkPBGe(coefficients: IntArray, literals: Array<Expr<BoolSort>>, k: Int): BoolExpr =
        BoolExpr(Z3_mk_pbge(context, literals.size.toUInt(), literals.native, coefficients.toCValues(), k)!!)

    public actual fun mkPBEq(coefficients: IntArray, literals: Array<Expr<BoolSort>>, k: Int): BoolExpr =
        BoolExpr(Z3_mk_pbeq(context, literals.size.toUInt(), literals.native, coefficients.toCValues(), k)!!)

    public actual fun <R : Sort> mkNumeral(value: String, sort: R): Expr<R> = Expr(
        Z3_mk_numeral(
            context,
            value,
            sort.native,
        )!!,
    )
    public actual fun <R : Sort> mkNumeral(value: Int, sort: R): Expr<R> = Expr(Z3_mk_int(context, value, sort.native)!!)
    public actual fun <R : Sort> mkNumeral(value: Long, sort: R): Expr<R> = Expr(Z3_mk_int64(context, value, sort.native)!!)
    public actual fun mkReal(numerator: Int, denominator: Int): RatNum = RatNum(Z3_mk_real(context, numerator, denominator)!!)
    public actual fun mkReal(value: String): RatNum = RatNum(Z3_mk_numeral(context, value, realSort.native)!!)
    public actual fun mkReal(value: Int): RatNum = RatNum(Z3_mk_int(context, value, realSort.native)!!)
    public actual fun mkReal(value: Long): RatNum = RatNum(Z3_mk_int64(context, value, realSort.native)!!)
    public actual fun mkInt(value: String): IntNum = IntNum(Z3_mk_numeral(context, value, intSort.native)!!)
    public actual fun mkInt(value: Int): IntNum = IntNum(Z3_mk_int(context, value, intSort.native)!!)
    public actual fun mkInt(value: Long): IntNum = IntNum(Z3_mk_int64(context, value, intSort.native)!!)
    public actual fun mkBV(value: String, size: Int): BitVecNum = BitVecNum(Z3_mk_numeral(context, value, mkBitVecSort(size).native)!!)
    public actual fun mkBV(value: Int, size: Int): BitVecNum = BitVecNum(Z3_mk_int(context, value, mkBitVecSort(size).native)!!)
    public actual fun mkBV(value: Long, size: Int): BitVecNum = BitVecNum(Z3_mk_int64(context, value, mkBitVecSort(size).native)!!)
    
    public actual fun mkForall(
        sorts: Array<Sort>,
        names: Array<Symbol>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier = mkQuantifier(true, sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID)

    public actual fun mkForall(
        boundConstants: Array<Expr<*>>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier = mkQuantifier(true, boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID)

    public actual fun mkExists(
        sorts: Array<Sort>,
        names: Array<Symbol>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier = mkQuantifier(false, sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID)

    public actual fun mkExists(
        boundConstants: Array<Expr<*>>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier = mkQuantifier(false, boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID)

    public actual fun mkQuantifier(
        isForall: Boolean,
        sorts: Array<Sort>,
        names: Array<Symbol>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier {
        check(sorts.size == names.size) { "sorts.size != names.size" }

        return Quantifier(if (patterns == null && quantifierID == null && skolemID == null) {
            Z3_mk_quantifier(
                context, isForall, weight.toUInt(),
                patterns.size.toUInt(), patterns?.native,
                sorts.size.toUInt(), sorts.native, names.native, body.native
            )
        } else {
            Z3_mk_quantifier_ex(
                context, isForall, weight.toUInt(),
                quantifierID?.native, skolemID?.native,
                patterns.size.toUInt(), patterns?.native,
                noPatterns.size.toUInt(), noPatterns?.native,
                sorts.size.toUInt(), sorts.native, names.native, body.native
            )
        }!!)
    }

    public actual fun mkQuantifier(
        isForall: Boolean,
        boundConstants: Array<Expr<*>>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier = Quantifier(if (patterns == null && quantifierID == null && skolemID == null) {
        Z3_mk_quantifier_const(
            context, isForall, weight.toUInt(),
            boundConstants.size.toUInt(), boundConstants.map { it.native as Z3_app }.toCValues(),
            patterns.size.toUInt(), patterns?.native,
            body.native
        )
    } else {
        Z3_mk_quantifier_const_ex(
            context, isForall, weight.toUInt(),
            quantifierID?.native, skolemID?.native,
            boundConstants.size.toUInt(), boundConstants.map { it.native as Z3_app }.toCValues(),
            patterns.size.toUInt(), patterns?.native,
            noPatterns.size.toUInt(), noPatterns?.native,
            body.native
        )
    }!!)

    public actual fun <R : Sort> mkLambda(sorts: Array<Sort>, names: Array<Symbol>, body: Expr<R>): Lambda<R> =
        Lambda(Z3_mk_lambda(context, sorts.size.toUInt(), sorts.native, names.native, body.native)!!)

    public actual fun <R : Sort> mkLambda(boundConstants: Array<Expr<*>>, body: Expr<R>): Lambda<R> =
        Lambda(Z3_mk_lambda_const(context, boundConstants.size.toUInt(), boundConstants.map { it.native as Z3_app }.toCValues(), body.native)!!)

    public actual fun setPrintMode(mode: AstPrintMode) {
        Z3_set_ast_print_mode(context, mode)
    }

    public actual fun benchmarkToSMTString(
        name: String,
        logic: String,
        status: String,
        attributes: String,
        assumptions: Array<Expr<BoolSort>>,
        formula: Expr<BoolSort>
    ): String = Z3_benchmark_to_smtlib_string(context, name, logic, status, attributes, assumptions.size.toUInt(), assumptions.native, formula.native)?.toKString() ?: ""

    public actual fun parseSMTLIB2String(
        string: String,
        sortNames: Array<Symbol>?,
        sorts: Array<Sort>?,
        declNames: Array<Symbol>?,
        decls: Array<FuncDecl<*>>?
    ): Array<BoolExpr> {
        val vector = Z3_parse_smtlib2_string(
            context, string,
            sortNames.size.toUInt(), sortNames?.native, sorts?.native,
            declNames.size.toUInt(), declNames?.native, decls?.native,
        )!!
        return Array(Z3_ast_vector_size(context, vector).toInt()) { BoolExpr(Z3_ast_vector_get(context, vector, it.toUInt())!!) }
    }

    public actual fun parseSMTLIB2File(
        file: String,
        sortNames: Array<Symbol>?,
        sorts: Array<Sort>?,
        declNames: Array<Symbol>?,
        decls: Array<FuncDecl<*>>?
    ): Array<BoolExpr> {
        val vector = Z3_parse_smtlib2_file(
            context, file,
            sortNames.size.toUInt(), sortNames?.native, sorts?.native,
            declNames.size.toUInt(), declNames?.native, decls?.native,
        )!!
        return Array(Z3_ast_vector_size(context, vector).toInt()) { BoolExpr(Z3_ast_vector_get(context, vector, it.toUInt())!!) }
    }

    public actual fun mkGoal(preciseSubgoals: Boolean, models: Boolean, unsatCores: Boolean): Goal = Goal(Z3_mk_goal(context, preciseSubgoals, models, unsatCores)!!, this)
    public actual fun mkParams(): Params = Params(Z3_mk_params(context)!!, this)
    public actual fun getNumTactics(): Int = Z3_get_num_tactics(context).toInt()
    public actual fun getTacticNames(): Array<String> = Array(getNumTactics()) { Z3_get_tactic_name(context, it.toUInt())?.toKString() ?: "" }
    public actual fun getTacticDescription(name: String): String = Z3_tactic_get_descr(context, name)?.toKString() ?: ""
    public actual fun mkTactic(name: String): Tactic = Tactic(Z3_mk_tactic(context, name)!!, this)
    public actual fun andThen(t1: Tactic, t2: Tactic, vararg rest: Tactic): Tactic = rest
        .fold(Z3_tactic_and_then(context, t1.native, t2.native)) { prev, current -> Z3_tactic_and_then(context, prev, current.native) }
        .let { Tactic(it!!, this) }

    public actual fun andThen(s1: Simplifier, s2: Simplifier, vararg rest: Simplifier): Simplifier = rest
        .fold(Z3_simplifier_and_then(context, s1.native, s2.native)) { prev, current -> Z3_simplifier_and_then(context, prev, current.native) }
        .let { Simplifier(it!!, this) }

    public actual fun then(t1: Tactic, t2: Tactic, vararg rest: Tactic): Tactic = andThen(t1, t2, *rest)
    public actual fun then(s1: Simplifier, s2: Simplifier, vararg rest: Simplifier): Simplifier = andThen(s1, s2, *rest)
    public actual fun orElse(t1: Tactic, t2: Tactic): Tactic = Tactic(Z3_tactic_or_else(context, t1.native, t2.native)!!, this)
    public actual fun tryFor(t: Tactic, milliseconds: Int): Tactic = Tactic(Z3_tactic_try_for(context, t.native, milliseconds.toUInt())!!, this)
    public actual fun `when`(p: Probe, t: Tactic): Tactic = Tactic(Z3_tactic_when(context, p.native, t.native)!!, this)
    public actual fun cond(p: Probe, thenTactic: Tactic, elseTactic: Tactic): Tactic = Tactic(Z3_tactic_cond(context, p.native, thenTactic.native, elseTactic.native)!!, this)
    public actual fun repeat(t: Tactic, max: Int): Tactic = Tactic(Z3_tactic_repeat(context, t.native, max.toUInt())!!, this)
    public actual fun skip(): Tactic = Tactic(Z3_tactic_skip(context)!!, this)
    public actual fun fail(): Tactic = Tactic(Z3_tactic_fail(context)!!, this)
    public actual fun failIf(p: Probe): Tactic = Tactic(Z3_tactic_fail_if(context, p.native)!!, this)
    public actual fun failIfNotDecided(): Tactic = Tactic(Z3_tactic_fail_if_not_decided(context)!!, this)
    public actual fun usingParams(t: Tactic, p: Params): Tactic = Tactic(Z3_tactic_using_params(context, t.native, p.native)!!, this)
    public actual fun usingParams(s: Simplifier, p: Params): Simplifier = Simplifier(Z3_simplifier_using_params(context, s.native, p.native)!!, this)
    public actual fun with(t: Tactic, p: Params): Tactic = usingParams(t, p)
    public actual fun with(s: Simplifier, p: Params): Simplifier = usingParams(s, p)
    public actual fun parOr(vararg tactics: Tactic): Tactic = Tactic(Z3_tactic_par_or(context, tactics.size.toUInt(), tactics.native)!!, this)
    public actual fun parAndThen(t1: Tactic, t2: Tactic): Tactic = Tactic(Z3_tactic_par_and_then(context, t1.native, t2.native)!!, this)

    public actual fun interrupt() {
        Z3_interrupt(context)
    }

    public actual fun getNumSimplifiers(): Int = Z3_get_num_simplifiers(context).toInt()
    public actual fun getSimplifierNames(): Array<String> = Array(getNumSimplifiers()) { Z3_get_simplifier_name(context, it.toUInt())?.toKString() ?: "" }
    public actual fun getSimplifierDescription(name: String): String = Z3_simplifier_get_descr(context, name)?.toKString() ?: ""
    public actual fun mkSimplifier(name: String): Simplifier = Simplifier(Z3_mk_simplifier(context, name)!!, this)
    public actual fun getNumProbes(): Int = Z3_get_num_probes(context).toInt()
    public actual fun getProbeNames(): Array<String> = Array(getNumProbes()) { Z3_get_probe_name(context, it.toUInt())?.toKString() ?: "" }
    public actual fun getProbeDescription(name: String): String = Z3_probe_get_descr(context, name)?.toKString() ?: ""
    public actual fun mkProbe(name: String): Probe = Probe(Z3_mk_probe(context, name)!!, this)
    public actual fun constProbe(value: Double): Probe = Probe(Z3_probe_const(context, value)!!, this)
    public actual fun lt(p1: Probe, p2: Probe): Probe = Probe(Z3_probe_lt(context, p1.native, p2.native)!!, this)
    public actual fun gt(p1: Probe, p2: Probe): Probe = Probe(Z3_probe_gt(context, p1.native, p2.native)!!, this)
    public actual fun le(p1: Probe, p2: Probe): Probe = Probe(Z3_probe_le(context, p1.native, p2.native)!!, this)
    public actual fun ge(p1: Probe, p2: Probe): Probe = Probe(Z3_probe_ge(context, p1.native, p2.native)!!, this)
    public actual fun eq(p1: Probe, p2: Probe): Probe = Probe(Z3_probe_eq(context, p1.native, p2.native)!!, this)
    public actual fun and(p1: Probe, p2: Probe): Probe = Probe(Z3_probe_and(context, p1.native, p2.native)!!, this)
    public actual fun or(p1: Probe, p2: Probe): Probe = Probe(Z3_probe_or(context, p1.native, p2.native)!!, this)
    public actual fun not(p: Probe): Probe = Probe(Z3_probe_not(context, p.native)!!, this)
    public actual fun mkSolver(): Solver = Solver(Z3_mk_solver(context)!!, this)
    public actual fun mkSolver(logic: Symbol): Solver = Solver(Z3_mk_solver_for_logic(context, logic.native)!!, this)
    public actual fun mkSolver(logic: String): Solver = mkSolver(mkSymbol(logic))
    public actual fun mkSolver(t: Tactic): Solver = Solver(Z3_mk_solver_from_tactic(context, t.native)!!, this)
    public actual fun mkSolver(s: Solver, simplifier: Simplifier): Solver = Solver(Z3_solver_add_simplifier(context, s.native, simplifier.native)!!, this)
    public actual fun mkSimpleSolver(): Solver = Solver(Z3_mk_simple_solver(context)!!, this)
    public actual fun mkFixedpoint(): Fixedpoint = Fixedpoint(Z3_mk_fixedpoint(context)!!, this)
    public actual fun mkOptimize(): Optimize = Optimize(Z3_mk_optimize(context)!!, this)

    public actual fun mkFPRoundingModeSort(): FPRMSort = FPRMSort(Z3_mk_fpa_rounding_mode_sort(context)!!)
    public actual fun mkFPRoundNearestTiesToEven(): FPRMExpr = FPRMExpr(Z3_mk_fpa_rne(context)!!)
    public actual fun mkFPRNE(): FPRMNum = FPRMNum(Z3_mk_fpa_rne(context)!!)
    public actual fun mkFPRoundNearestTiesToAway(): FPRMNum = FPRMNum(Z3_mk_fpa_rna(context)!!)
    public actual fun mkFPRNA(): FPRMNum = FPRMNum(Z3_mk_fpa_rna(context)!!)
    public actual fun mkFPRoundTowardPositive(): FPRMNum = FPRMNum(Z3_mk_fpa_rtp(context)!!)
    public actual fun mkFPRTP(): FPRMNum = FPRMNum(Z3_mk_fpa_rtp(context)!!)
    public actual fun mkFPRoundTowardNegative(): FPRMNum = FPRMNum(Z3_mk_fpa_rtn(context)!!)
    public actual fun mkFPRTN(): FPRMNum = FPRMNum(Z3_mk_fpa_rtn(context)!!)
    public actual fun mkFPRoundTowardZero(): FPRMNum = FPRMNum(Z3_mk_fpa_rtz(context)!!)
    public actual fun mkFPRTZ(): FPRMNum = FPRMNum(Z3_mk_fpa_rtz(context)!!)
    public actual fun mkFPSort(exponentBits: Int, significandBits: Int): FPSort = FPSort(Z3_mk_fpa_sort(context, exponentBits.toUInt(), significandBits.toUInt())!!)
    public actual fun mkFPSortHalf(): FPSort = mkFPSort16()
    public actual fun mkFPSort16(): FPSort = FPSort(Z3_mk_fpa_sort_16(context)!!)
    public actual fun mkFPSortSingle(): FPSort = mkFPSort32()
    public actual fun mkFPSort32(): FPSort = FPSort(Z3_mk_fpa_sort_32(context)!!)
    public actual fun mkFPSortDouble(): FPSort = mkFPSort64()
    public actual fun mkFPSort64(): FPSort = FPSort(Z3_mk_fpa_sort_64(context)!!)
    public actual fun mkFPSortQuadruple(): FPSort = mkFPSort128()
    public actual fun mkFPSort128(): FPSort = FPSort(Z3_mk_fpa_sort_128(context)!!)
    public actual fun mkFPNaN(sort: FPSort): FPNum = FPNum(Z3_mk_fpa_nan(context, sort.native)!!)
    public actual fun mkFPInf(sort: FPSort, negative: Boolean): FPNum = FPNum(Z3_mk_fpa_inf(context, sort.native, negative)!!)
    public actual fun mkFPZero(sort: FPSort, negative: Boolean): FPNum = FPNum(Z3_mk_fpa_zero(context, sort.native, negative)!!)
    public actual fun mkFPNumeral(value: Float, sort: FPSort): FPNum = FPNum(Z3_mk_fpa_numeral_float(context, value, sort.native)!!)
    public actual fun mkFPNumeral(value: Double, sort: FPSort): FPNum = FPNum(Z3_mk_fpa_numeral_double(context, value, sort.native)!!)
    public actual fun mkFPNumeral(value: Int, sort: FPSort): FPNum = FPNum(Z3_mk_fpa_numeral_int(context, value, sort.native)!!)

    public actual fun mkFPNumeral(sign: Boolean, significand: Int, exponent: Int, sort: FPSort): FPNum =
        FPNum(Z3_mk_fpa_numeral_int_uint(context, sign, significand, exponent.toUInt(), sort.native)!!)

    public actual fun mkFPNumeral(sign: Boolean, significand: Long, exponent: Long, sort: FPSort): FPNum =
        FPNum(Z3_mk_fpa_numeral_int64_uint64(context, sign, significand, exponent.toULong(), sort.native)!!)

    public actual fun mkFP(value: Float, sort: FPSort): FPNum = mkFPNumeral(value, sort)
    public actual fun mkFP(value: Double, sort: FPSort): FPNum = mkFPNumeral(value, sort)
    public actual fun mkFP(value: Int, sort: FPSort): FPNum = mkFPNumeral(value, sort)
    public actual fun mkFP(sign: Boolean, significand: Int, exponent: Int, sort: FPSort): FPNum = mkFPNumeral(sign, significand, exponent, sort)
    public actual fun mkFP(sign: Boolean, significand: Long, exponent: Long, sort: FPSort): FPNum = mkFPNumeral(sign, significand, exponent, sort)

    public actual fun mkFP(sign: Expr<BitVecSort>, exponent: Expr<BitVecSort>, significand: Expr<BitVecSort>): FPExpr =
        FPExpr(Z3_mk_fpa_fp(context, sign.native, exponent.native, significand.native)!!)

    public actual fun mkFPAbs(expr: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_abs(context, expr.native)!!)
    public actual fun mkFPNeg(expr: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_neg(context, expr.native)!!)
    public actual fun mkFPAdd(rm: Expr<FPRMSort>, left: Expr<FPSort>, right: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_add(context, rm.native, left.native, right.native)!!)
    public actual fun mkFPSub(rm: Expr<FPRMSort>, left: Expr<FPSort>, right: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_sub(context, rm.native, left.native, right.native)!!)
    public actual fun mkFPMul(rm: Expr<FPRMSort>, left: Expr<FPSort>, right: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_mul(context, rm.native, left.native, right.native)!!)
    public actual fun mkFPDiv(rm: Expr<FPRMSort>, left: Expr<FPSort>, right: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_div(context, rm.native, left.native, right.native)!!)
    public actual fun mkFPFMA(rm: Expr<FPRMSort>, t1: Expr<FPSort>, t2: Expr<FPSort>, t3: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_fma(context, rm.native, t1.native, t2.native, t3.native)!!)
    public actual fun mkFPSqrt(rm: Expr<FPRMSort>, expr: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_sqrt(context, rm.native, expr.native)!!)
    public actual fun mkFPRem(left: Expr<FPSort>, right: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_rem(context, left.native, right.native)!!)
    public actual fun mkFPRoundToIntegral(rm: Expr<FPRMSort>, expr: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_round_to_integral(context, rm.native, expr.native)!!)
    public actual fun mkFPMin(left: Expr<FPSort>, right: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_min(context, left.native, right.native)!!)
    public actual fun mkFPMax(left: Expr<FPSort>, right: Expr<FPSort>): FPExpr = FPExpr(Z3_mk_fpa_max(context, left.native, right.native)!!)
    public actual fun mkFPLEq(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_leq(context, left.native, right.native)!!)
    public actual fun mkFPLt(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_lt(context, left.native, right.native)!!)
    public actual fun mkFPGEq(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_geq(context, left.native, right.native)!!)
    public actual fun mkFPGt(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_gt(context, left.native, right.native)!!)
    public actual fun mkFPEq(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_eq(context, left.native, right.native)!!)
    public actual fun mkFPIsNormal(expr: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_is_normal(context, expr.native)!!)
    public actual fun mkFPIsSubnormal(expr: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_is_subnormal(context, expr.native)!!)
    public actual fun mkFPIsZero(expr: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_is_zero(context, expr.native)!!)
    public actual fun mkFPIsInfinite(expr: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_is_infinite(context, expr.native)!!)
    public actual fun mkFPIsNaN(expr: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_is_nan(context, expr.native)!!)
    public actual fun mkFPIsNegative(expr: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_is_negative(context, expr.native)!!)
    public actual fun mkFPIsPositive(expr: Expr<FPSort>): BoolExpr = BoolExpr(Z3_mk_fpa_is_positive(context, expr.native)!!)
    public actual fun mkFPToFP(bv: Expr<BitVecSort>, sort: FPSort): FPExpr = FPExpr(Z3_mk_fpa_to_fp_bv(context, bv.native, sort.native)!!)
    public actual fun mkFPToFP(rm: Expr<FPRMSort>, expr: FPExpr, sort: FPSort): FPExpr = FPExpr(Z3_mk_fpa_to_fp_float(context, rm.native, expr.native, sort.native)!!)
    public actual fun mkFPToFP(rm: Expr<FPRMSort>, expr: RealExpr, sort: FPSort): FPExpr = FPExpr(Z3_mk_fpa_to_fp_real(context, rm.native, expr.native, sort.native)!!)

    public actual fun mkFPToFP(rm: Expr<FPRMSort>, expr: Expr<BitVecSort>, sort: FPSort, isSigned: Boolean): FPExpr =
        if (isSigned) FPExpr(Z3_mk_fpa_to_fp_signed(context, rm.native, expr.native, sort.native)!!)
        else FPExpr(Z3_mk_fpa_to_fp_unsigned(context, rm.native, expr.native, sort.native)!!)

    public actual fun mkFPToFP(sort: FPSort, rm: Expr<FPRMSort>, expr: Expr<FPSort>): FPExpr =
        FPExpr(Z3_mk_fpa_to_fp_float(context, rm.native, expr.native, sort.native)!!)

    public actual fun mkFPToFP(rm: Expr<FPRMSort>, sgn: Expr<IntSort>, exp: Expr<RealSort>, sort: FPSort): BitVecExpr =
        BitVecExpr(Z3_mk_fpa_to_fp_int_real(context, rm.native, sgn.native, exp.native, sort.native)!!)

    public actual fun mkFPToBV(rm: Expr<FPRMSort>, expr: Expr<FPSort>, size: Int, isSigned: Boolean): BitVecExpr =
        if (isSigned) BitVecExpr(Z3_mk_fpa_to_sbv(context, rm.native, expr.native, size.toUInt())!!)
        else BitVecExpr(Z3_mk_fpa_to_ubv(context, rm.native, expr.native, size.toUInt())!!)

    public actual fun mkFPToReal(expr: Expr<FPSort>): RealExpr =
        RealExpr(Z3_mk_fpa_to_real(context, expr.native)!!)

    public actual fun mkFPToIEEEBV(expr: Expr<FPSort>): BitVecExpr =
        BitVecExpr(Z3_mk_fpa_to_ieee_bv(context, expr.native)!!)

    public actual fun <R : Sort> mkLinearOrder(sort: R, index: Int): FuncDecl<BoolSort> =
        FuncDecl(Z3_mk_linear_order(context, sort.native, index.toUInt())!!)

    public actual fun <R : Sort> mkPartialOrder(sort: R, index: Int): FuncDecl<BoolSort> =
        FuncDecl(Z3_mk_partial_order(context, sort.native, index.toUInt())!!)

    public actual fun SimplifyHelp(): String = Z3_simplify_get_help(context)!!.toKString()
    public actual fun getSimplifyParameterDescriptions(): ParamDescriptions = ParamDescriptions(Z3_simplify_get_param_descrs(context)!!, this)
    public actual fun updateParamValue(key: String, value: String): Unit = Z3_update_param_value(context, key, value)

    public actual override fun close() {
        if (context == null) return
        Z3_del_context(context)
        context = null
    }
    
    public override fun toString(): String = "Z3Context(native=$context)"
}
