@file:Suppress("unused", "FunctionName")
package com.sschr15.z3kt

import kotlin.jvm.JvmField

public expect class Context : AutoCloseable {
    public constructor()
    public constructor(config: Map<String, String>)

    public fun mkSymbol(id: Int): IntSymbol
    public fun mkSymbol(name: String): StringSymbol

    public fun getBoolSort(): BoolSort
    public fun getIntSort(): IntSort
    public fun getRealSort(): RealSort
    public fun mkBoolSort(): BoolSort
    public fun mkCharSort(): CharSort
    public fun getStringSort(): SeqSort<CharSort>
    public fun mkUninterpretedSort(s: Symbol): UninterpretedSort
    public fun mkUninterpretedSort(name: String): UninterpretedSort
    public fun mkIntSort(): IntSort
    public fun mkRealSort(): RealSort
    public fun mkBitVecSort(size: Int): BitVecSort

    public fun <D : Sort, R : Sort> mkArraySort(domain: D, range: R): ArraySort<D, R>
    public fun <R : Sort> mkArraySort(domain: Array<Sort>, range: R): ArraySort<Sort, R>
    public fun mkStringSort(): SeqSort<CharSort>
    public fun <R : Sort> mkSeqSort(elementSort: R): SeqSort<R>
    public fun <R : Sort> mkReSort(elementSort: R): ReSort<R>
    public fun mkTupleSort(name: Symbol, fieldNames: Array<Symbol>, fieldSorts: Array<Sort>): TupleSort

    public fun <R> mkEnumSort(name: Symbol, vararg enumNames: Symbol): EnumSort<R>
    public fun <R> mkEnumSort(name: String, vararg enumNames: String): EnumSort<R>
    public fun <R : Sort> mkListSort(name: Symbol, elementSort: R): ListSort<R>
    public fun <R : Sort> mkListSort(name: String, elementSort: R): ListSort<R>
    public fun <R> mkFiniteDomainSort(name: Symbol, size: Long): FiniteDomainSort<R>
    public fun <R> mkFiniteDomainSort(name: String, size: Long): FiniteDomainSort<R>

    public fun <R> mkConstructor(
        name: Symbol,
        recognizer: Symbol,
        fieldNames: Array<Symbol>,
        sorts: Array<Sort>,
        sortRefs: IntArray
    ): Constructor<R>

    public fun <R> mkConstructor(
        name: String,
        recognizer: String,
        fieldNames: Array<String>,
        sorts: Array<Sort>,
        sortRefs: IntArray
    ): Constructor<R>

    public fun <R> mkDatatypeSort(name: Symbol, constructors: Array<Constructor<R>>): DatatypeSort<R>
    public fun <R> mkDatatypeSort(name: String, constructors: Array<Constructor<R>>): DatatypeSort<R>

    public fun mkDatatypeSorts(
        names: Array<Symbol>,
        constructors: Array<Array<Constructor<Any>>>
    ): Array<DatatypeSort<Any>>

    public fun mkDatatypeSorts(
        names: Array<String>,
        constructors: Array<Array<Constructor<Any>>>
    ): Array<DatatypeSort<Any>>

    public fun <F : Sort, R : Sort> mkUpdateField(
        accessor: FuncDecl<F>,
        value: Expr<R>,
        field: Expr<F>
    ): Expr<R>

    public fun <R : Sort> mkFuncDecl(name: Symbol, domain: Array<Sort>, range: R): FuncDecl<R>
    public fun <R : Sort> mkPropagateFunction(name: Symbol, domain: Array<Sort>, range: R): FuncDecl<R>
    public fun <R : Sort> mkFuncDecl(name: Symbol, domain: Sort, range: R): FuncDecl<R>
    public fun <R : Sort> mkFuncDecl(name: String, domain: Array<Sort>, range: R): FuncDecl<R>
    public fun <R : Sort> mkFuncDecl(name: String, domain: Sort, range: R): FuncDecl<R>
    public fun <R : Sort> mkRecFuncDecl(name: Symbol, domain: Array<Sort>, range: R): FuncDecl<R>
    public fun <R : Sort> AddRecDef(f: FuncDecl<R>, args: Array<Expr<*>>, body: Expr<R>)
    public fun <R : Sort> mkFreshFuncDecl(prefix: String, domain: Array<Sort>, range: R): FuncDecl<R>
    public fun <R : Sort> mkConstDecl(name: Symbol, sort: R): FuncDecl<R>
    public fun <R : Sort> mkConstDecl(name: String, sort: R): FuncDecl<R>
    public fun <R : Sort> mkFreshConstDecl(prefix: String, sort: R): FuncDecl<R>
    public fun <R : Sort> mkBound(index: Int, sort: R): Expr<R>
    public fun mkPattern(vararg terms: Expr<*>): Pattern
    public fun <R : Sort> mkConst(s: Symbol, sort: R): Expr<R>
    public fun <R : Sort> mkConst(name: String, sort: R): Expr<R>
    public fun <R : Sort> mkFreshConst(prefix: String, sort: R): Expr<R>
    public fun <R : Sort> mkConst(decl: FuncDecl<R>): Expr<R>
    public fun mkBoolConst(s: Symbol): BoolExpr
    public fun mkBoolConst(name: String): BoolExpr
    public fun mkIntConst(s: Symbol): IntExpr
    public fun mkIntConst(name: String): IntExpr
    public fun mkRealConst(s: Symbol): RealExpr
    public fun mkRealConst(name: String): RealExpr
    public fun mkBVConst(s: Symbol, size: Int): BitVecExpr
    public fun mkBVConst(name: String, size: Int): BitVecExpr
    public fun <R : Sort> mkApp(f: FuncDecl<R>, vararg args: Expr<*>): Expr<R>

    public fun mkTrue(): BoolExpr
    public fun mkFalse(): BoolExpr
    public fun mkBool(value: Boolean): BoolExpr
    public fun mkEq(left: Expr<*>, right: Expr<*>): BoolExpr
    public fun mkDistinct(vararg args: Expr<*>): BoolExpr
    public fun mkNot(expr: Expr<BoolSort>): BoolExpr
    public fun <R : Sort> mkITE(
        condition: Expr<BoolSort>,
        thenExpr: Expr<out R>,
        elseExpr: Expr<out R>
    ): Expr<R>

    public fun mkIff(left: Expr<BoolSort>, right: Expr<BoolSort>): BoolExpr
    public fun mkImplies(left: Expr<BoolSort>, right: Expr<BoolSort>): BoolExpr
    public fun mkXor(left: Expr<BoolSort>, right: Expr<BoolSort>): BoolExpr
    public fun mkAnd(vararg args: Expr<BoolSort>): BoolExpr
    public fun mkOr(vararg args: Expr<BoolSort>): BoolExpr

    public fun <R : ArithSort> mkAdd(vararg args: Expr<out R>): ArithExpr<R>
    public fun <R : ArithSort> mkMul(vararg args: Expr<out R>): ArithExpr<R>
    public fun <R : ArithSort> mkSub(vararg args: Expr<out R>): ArithExpr<R>
    public fun <R : ArithSort> mkUnaryMinus(expr: Expr<R>): ArithExpr<R>
    public fun <R : ArithSort> mkDiv(numerator: Expr<out R>, denominator: Expr<out R>): ArithExpr<R>

    public fun mkMod(left: Expr<IntSort>, right: Expr<IntSort>): IntExpr
    public fun mkRem(left: Expr<IntSort>, right: Expr<IntSort>): IntExpr
    public fun <R : ArithSort> mkPower(base: Expr<out R>, exponent: Expr<out R>): ArithExpr<R>

    public fun mkLt(left: Expr<out ArithSort>, right: Expr<out ArithSort>): BoolExpr
    public fun mkLe(left: Expr<out ArithSort>, right: Expr<out ArithSort>): BoolExpr
    public fun mkGt(left: Expr<out ArithSort>, right: Expr<out ArithSort>): BoolExpr
    public fun mkGe(left: Expr<out ArithSort>, right: Expr<out ArithSort>): BoolExpr

    public fun mkInt2Real(expr: Expr<IntSort>): RealExpr
    public fun mkReal2Int(expr: Expr<RealSort>): IntExpr
    public fun mkIsInteger(expr: Expr<RealSort>): BoolExpr

    // BitVector operations
    public fun mkBVNot(expr: Expr<BitVecSort>): BitVecExpr
    public fun mkBVRedAND(expr: Expr<BitVecSort>): BitVecExpr
    public fun mkBVRedOR(expr: Expr<BitVecSort>): BitVecExpr
    public fun mkBVAND(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVOR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVXOR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVNAND(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVNOR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVXNOR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVNeg(expr: Expr<BitVecSort>): BitVecExpr
    public fun mkBVAdd(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVSub(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVMul(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVUDiv(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVSDiv(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVURem(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVSRem(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVSMod(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr

    public fun mkBVULT(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVSLT(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVULE(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVSLE(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVUGE(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVSGE(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVUGT(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVSGT(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr

    public fun mkConcat(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkExtract(high: Int, low: Int, expr: Expr<BitVecSort>): BitVecExpr
    public fun mkSignExt(count: Int, expr: Expr<BitVecSort>): BitVecExpr
    public fun mkZeroExt(count: Int, expr: Expr<BitVecSort>): BitVecExpr
    public fun mkRepeat(count: Int, expr: Expr<BitVecSort>): BitVecExpr
    public fun mkBVSHL(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVLSHR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVASHR(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVRotateLeft(count: Int, expr: Expr<BitVecSort>): BitVecExpr
    public fun mkBVRotateRight(count: Int, expr: Expr<BitVecSort>): BitVecExpr
    public fun mkBVRotateLeft(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr
    public fun mkBVRotateRight(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BitVecExpr

    public fun mkInt2BV(size: Int, expr: Expr<IntSort>): BitVecExpr
    public fun mkBV2Int(expr: Expr<BitVecSort>, isSigned: Boolean): IntExpr

    public fun mkBVAddNoOverflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>, isSigned: Boolean): BoolExpr
    public fun mkBVAddNoUnderflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVSubNoOverflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVSubNoUnderflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>, isSigned: Boolean): BoolExpr
    public fun mkBVSDivNoOverflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr
    public fun mkBVNegNoOverflow(expr: Expr<BitVecSort>): BoolExpr
    public fun mkBVMulNoOverflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>, isSigned: Boolean): BoolExpr
    public fun mkBVMulNoUnderflow(left: Expr<BitVecSort>, right: Expr<BitVecSort>): BoolExpr

    // Array operations
    public fun <D : Sort, R : Sort> mkArrayConst(name: Symbol, domain: D, range: R): ArrayExpr<D, R>
    public fun <D : Sort, R : Sort> mkArrayConst(name: String, domain: D, range: R): ArrayExpr<D, R>
    public fun <D : Sort, R : Sort> mkSelect(array: Expr<ArraySort<D, R>>, index: Expr<D>): Expr<R>
    public fun <R : Sort> mkSelect(array: Expr<ArraySort<Sort, R>>, indices: Array<Expr<*>>): Expr<R>
    public fun <D : Sort, R : Sort> mkStore(
        array: Expr<ArraySort<D, R>>,
        index: Expr<D>,
        value: Expr<R>
    ): ArrayExpr<D, R>

    public fun <R : Sort> mkStore(
        array: Expr<ArraySort<Sort, R>>,
        indices: Array<Expr<*>>,
        value: Expr<R>
    ): ArrayExpr<Sort, R>

    public fun <D : Sort, R : Sort> mkConstArray(domain: D, value: Expr<R>): ArrayExpr<D, R>

    public fun <D : Sort, R1 : Sort, R2 : Sort> mkMap(
        f: FuncDecl<R2>,
        vararg arrays: Expr<ArraySort<D, R1>>
    ): ArrayExpr<D, R2>

    public fun <D : Sort, R : Sort> mkTermArray(array: Expr<ArraySort<D, R>>): Expr<R>
    public fun <D : Sort, R : Sort> mkArrayExt(
        left: Expr<ArraySort<D, R>>,
        right: Expr<ArraySort<D, R>>
    ): Expr<D>

    // Set operations
    public fun <D : Sort> mkSetSort(elementSort: D): SetSort<D>
    public fun <D : Sort> mkEmptySet(elementSort: D): ArrayExpr<D, BoolSort>
    public fun <D : Sort> mkFullSet(elementSort: D): ArrayExpr<D, BoolSort>
    public fun <D : Sort> mkSetAdd(
        set: Expr<ArraySort<D, BoolSort>>,
        element: Expr<D>
    ): ArrayExpr<D, BoolSort>

    public fun <D : Sort> mkSetDel(
        set: Expr<ArraySort<D, BoolSort>>,
        element: Expr<D>
    ): ArrayExpr<D, BoolSort>

    public fun <D : Sort> mkSetUnion(
        vararg sets: Expr<ArraySort<D, BoolSort>>
    ): ArrayExpr<D, BoolSort>

    public fun <D : Sort> mkSetIntersection(
        vararg sets: Expr<ArraySort<D, BoolSort>>
    ): ArrayExpr<D, BoolSort>

    public fun <D : Sort> mkSetDifference(
        left: Expr<ArraySort<D, BoolSort>>,
        right: Expr<ArraySort<D, BoolSort>>
    ): ArrayExpr<D, BoolSort>

    public fun <D : Sort> mkSetComplement(set: Expr<ArraySort<D, BoolSort>>): ArrayExpr<D, BoolSort>

    public fun <D : Sort> mkSetMembership(
        element: Expr<D>,
        set: Expr<ArraySort<D, BoolSort>>
    ): BoolExpr

    public fun <D : Sort> mkSetSubset(
        subset: Expr<ArraySort<D, BoolSort>>,
        superset: Expr<ArraySort<D, BoolSort>>
    ): BoolExpr

    // Sequence operations
    public fun <R : Sort> mkEmptySeq(sort: R): SeqExpr<R>
    public fun <R : Sort> mkUnit(expr: Expr<R>): SeqExpr<R>
    public fun mkString(s: String): SeqExpr<CharSort>
    public fun intToString(expr: Expr<IntSort>): SeqExpr<CharSort>
    public fun ubvToString(expr: Expr<BitVecSort>): SeqExpr<CharSort>
    public fun sbvToString(expr: Expr<BitVecSort>): SeqExpr<CharSort>
    public fun stringToInt(expr: Expr<SeqSort<CharSort>>): IntExpr
    public fun <R : Sort> mkConcat(vararg sequences: Expr<SeqSort<R>>): SeqExpr<R>
    public fun <R : Sort> mkLength(sequence: Expr<SeqSort<R>>): IntExpr
    public fun <R : Sort> mkPrefixOf(
        prefix: Expr<SeqSort<R>>,
        sequence: Expr<SeqSort<R>>
    ): BoolExpr

    public fun <R : Sort> mkSuffixOf(
        suffix: Expr<SeqSort<R>>,
        sequence: Expr<SeqSort<R>>
    ): BoolExpr

    public fun <R : Sort> mkContains(
        sequence: Expr<SeqSort<R>>,
        subsequence: Expr<SeqSort<R>>
    ): BoolExpr

    public fun MkStringLt(
        left: Expr<SeqSort<CharSort>>,
        right: Expr<SeqSort<CharSort>>
    ): BoolExpr

    public fun MkStringLe(
        left: Expr<SeqSort<CharSort>>,
        right: Expr<SeqSort<CharSort>>
    ): BoolExpr

    public fun <R : Sort> mkAt(
        sequence: Expr<SeqSort<R>>,
        index: Expr<IntSort>
    ): SeqExpr<R>

    public fun <R : Sort> mkNth(
        sequence: Expr<SeqSort<R>>,
        index: Expr<IntSort>
    ): Expr<R>

    public fun <R : Sort> mkExtract(
        sequence: Expr<SeqSort<R>>,
        offset: Expr<IntSort>,
        length: Expr<IntSort>
    ): SeqExpr<R>

    public fun <R : Sort> mkIndexOf(
        sequence: Expr<SeqSort<R>>,
        subsequence: Expr<SeqSort<R>>,
        offset: Expr<IntSort>
    ): IntExpr

    public fun <R : Sort> mkReplace(
        sequence: Expr<SeqSort<R>>,
        src: Expr<SeqSort<R>>,
        dst: Expr<SeqSort<R>>
    ): SeqExpr<R>

    // Regular expressions
    public fun <R : Sort> mkToRe(sequence: Expr<SeqSort<R>>): ReExpr<SeqSort<R>>
    public fun <R : Sort> mkInRe(sequence: Expr<SeqSort<R>>, regex: ReExpr<SeqSort<R>>): BoolExpr
    public fun <R : Sort> mkStar(regex: Expr<ReSort<R>>): ReExpr<R>
    public fun <R : Sort> mkPower(regex: Expr<ReSort<R>>, count: Int): ReExpr<R>
    public fun <R : Sort> mkLoop(regex: Expr<ReSort<R>>, min: Int, max: Int): ReExpr<R>
    public fun <R : Sort> mkLoop(regex: Expr<ReSort<R>>, count: Int): ReExpr<R>
    public fun <R : Sort> mkPlus(regex: Expr<ReSort<R>>): ReExpr<R>
    public fun <R : Sort> mkOption(regex: Expr<ReSort<R>>): ReExpr<R>
    public fun <R : Sort> mkComplement(regex: Expr<ReSort<R>>): ReExpr<R>
    public fun <R : Sort> mkConcat(vararg regexes: ReExpr<R>): ReExpr<R>
    public fun <R : Sort> mkUnion(vararg regexes: Expr<ReSort<R>>): ReExpr<R>
    public fun <R : Sort> mkIntersect(vararg regexes: Expr<ReSort<R>>): ReExpr<R>
    public fun <R : Sort> mkDiff(left: Expr<ReSort<R>>, right: Expr<ReSort<R>>): ReExpr<R>
    public fun <R : Sort> mkEmptyRe(sort: ReSort<R>): ReExpr<R>
    public fun <R : Sort> mkFullRe(sort: ReSort<R>): ReExpr<R>
    public fun <R : Sort> mkAllcharRe(sort: ReSort<R>): ReExpr<R>

    public fun mkRange(
        from: Expr<SeqSort<CharSort>>,
        to: Expr<SeqSort<CharSort>>
    ): ReExpr<SeqSort<CharSort>>

    // Character operations
    public fun mkCharLe(left: Expr<CharSort>, right: Expr<CharSort>): BoolExpr
    public fun charToInt(char: Expr<CharSort>): IntExpr
    public fun charToBv(char: Expr<CharSort>): BitVecExpr
    public fun charFromBv(bv: BitVecExpr): Expr<CharSort>
    public fun mkIsDigit(char: Expr<CharSort>): BoolExpr

    // Pseudo-boolean constraints
    public fun mkAtMost(literals: Array<Expr<BoolSort>>, k: Int): BoolExpr
    public fun mkAtLeast(literals: Array<Expr<BoolSort>>, k: Int): BoolExpr
    public fun mkPBLe(coefficients: IntArray, literals: Array<Expr<BoolSort>>, k: Int): BoolExpr
    public fun mkPBGe(coefficients: IntArray, literals: Array<Expr<BoolSort>>, k: Int): BoolExpr
    public fun mkPBEq(coefficients: IntArray, literals: Array<Expr<BoolSort>>, k: Int): BoolExpr

    // Numerals
    public fun <R : Sort> mkNumeral(value: String, sort: R): Expr<R>
    public fun <R : Sort> mkNumeral(value: Int, sort: R): Expr<R>
    public fun <R : Sort> mkNumeral(value: Long, sort: R): Expr<R>

    public fun mkReal(numerator: Int, denominator: Int): RatNum
    public fun mkReal(value: String): RatNum
    public fun mkReal(value: Int): RatNum
    public fun mkReal(value: Long): RatNum

    public fun mkInt(value: String): IntNum
    public fun mkInt(value: Int): IntNum
    public fun mkInt(value: Long): IntNum

    public fun mkBV(value: String, size: Int): BitVecNum
    public fun mkBV(value: Int, size: Int): BitVecNum
    public fun mkBV(value: Long, size: Int): BitVecNum

    // Quantifiers
    public fun mkForall(
        sorts: Array<Sort>,
        names: Array<Symbol>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier

    public fun mkForall(
        boundConstants: Array<Expr<*>>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier

    public fun mkExists(
        sorts: Array<Sort>,
        names: Array<Symbol>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier

    public fun mkExists(
        boundConstants: Array<Expr<*>>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier

    public fun mkQuantifier(
        isForall: Boolean,
        sorts: Array<Sort>,
        names: Array<Symbol>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier

    public fun mkQuantifier(
        isForall: Boolean,
        boundConstants: Array<Expr<*>>,
        body: Expr<BoolSort>,
        weight: Int,
        patterns: Array<Pattern>?,
        noPatterns: Array<Expr<*>>?,
        quantifierID: Symbol?,
        skolemID: Symbol?
    ): Quantifier

    public fun <R : Sort> mkLambda(
        sorts: Array<Sort>,
        names: Array<Symbol>,
        body: Expr<R>
    ): Lambda<R>

    public fun <R : Sort> mkLambda(boundConstants: Array<Expr<*>>, body: Expr<R>): Lambda<R>

    // Printing
    public fun setPrintMode(mode: AstPrintMode)

    public fun benchmarkToSMTString(
        name: String,
        logic: String,
        status: String,
        attributes: String,
        assumptions: Array<Expr<BoolSort>>,
        formula: Expr<BoolSort>
    ): String

    public fun parseSMTLIB2String(
        string: String,
        sortNames: Array<Symbol>?,
        sorts: Array<Sort>?,
        declNames: Array<Symbol>?,
        decls: Array<FuncDecl<*>>?
    ): Array<BoolExpr>

    public fun parseSMTLIB2File(
        file: String,
        sortNames: Array<Symbol>?,
        sorts: Array<Sort>?,
        declNames: Array<Symbol>?,
        decls: Array<FuncDecl<*>>?
    ): Array<BoolExpr>

    // Goals, tactics, and solvers
    public fun mkGoal(preciseSubgoals: Boolean, models: Boolean, unsatCores: Boolean): Goal
    public fun mkParams(): Params
    public fun getNumTactics(): Int
    public fun getTacticNames(): Array<String>
    public fun getTacticDescription(name: String): String
    public fun mkTactic(name: String): Tactic
    public fun andThen(t1: Tactic, t2: Tactic, vararg rest: Tactic): Tactic
    public fun then(t1: Tactic, t2: Tactic, vararg rest: Tactic): Tactic
    public fun orElse(t1: Tactic, t2: Tactic): Tactic
    public fun tryFor(t: Tactic, milliseconds: Int): Tactic
    public fun `when`(p: Probe, t: Tactic): Tactic
    public fun cond(p: Probe, thenTactic: Tactic, elseTactic: Tactic): Tactic
    public fun repeat(t: Tactic, max: Int): Tactic
    public fun skip(): Tactic
    public fun fail(): Tactic
    public fun failIf(p: Probe): Tactic
    public fun failIfNotDecided(): Tactic
    public fun usingParams(t: Tactic, p: Params): Tactic
    public fun with(t: Tactic, p: Params): Tactic
    public fun parOr(vararg tactics: Tactic): Tactic
    public fun parAndThen(t1: Tactic, t2: Tactic): Tactic

    public fun interrupt()

    // Simplifiers
    public fun getNumSimplifiers(): Int
    public fun getSimplifierNames(): Array<String>
    public fun getSimplifierDescription(name: String): String
    public fun mkSimplifier(name: String): Simplifier
    public fun andThen(s1: Simplifier, s2: Simplifier, vararg rest: Simplifier): Simplifier
    public fun then(s1: Simplifier, s2: Simplifier, vararg rest: Simplifier): Simplifier
    public fun usingParams(s: Simplifier, p: Params): Simplifier
    public fun with(s: Simplifier, p: Params): Simplifier

    // Probes
    public fun getNumProbes(): Int
    public fun getProbeNames(): Array<String>
    public fun getProbeDescription(name: String): String
    public fun mkProbe(name: String): Probe
    public fun constProbe(value: Double): Probe
    public fun lt(p1: Probe, p2: Probe): Probe
    public fun gt(p1: Probe, p2: Probe): Probe
    public fun le(p1: Probe, p2: Probe): Probe
    public fun ge(p1: Probe, p2: Probe): Probe
    public fun eq(p1: Probe, p2: Probe): Probe
    public fun and(p1: Probe, p2: Probe): Probe
    public fun or(p1: Probe, p2: Probe): Probe
    public fun not(p: Probe): Probe

    // Solvers
    public fun mkSolver(): Solver
    public fun mkSolver(logic: Symbol): Solver
    public fun mkSolver(logic: String): Solver
    public fun mkSimpleSolver(): Solver
    public fun mkSolver(t: Tactic): Solver
    public fun mkSolver(s: Solver, simplifier: Simplifier): Solver
    public fun mkFixedpoint(): Fixedpoint
    public fun mkOptimize(): Optimize

    // Floating-point
    public fun mkFPRoundingModeSort(): FPRMSort
    public fun mkFPRoundNearestTiesToEven(): FPRMExpr
    public fun mkFPRNE(): FPRMNum
    public fun mkFPRoundNearestTiesToAway(): FPRMNum
    public fun mkFPRNA(): FPRMNum
    public fun mkFPRoundTowardPositive(): FPRMNum
    public fun mkFPRTP(): FPRMNum
    public fun mkFPRoundTowardNegative(): FPRMNum
    public fun mkFPRTN(): FPRMNum
    public fun mkFPRoundTowardZero(): FPRMNum
    public fun mkFPRTZ(): FPRMNum

    public fun mkFPSort(exponentBits: Int, significandBits: Int): FPSort
    public fun mkFPSortHalf(): FPSort
    public fun mkFPSort16(): FPSort
    public fun mkFPSortSingle(): FPSort
    public fun mkFPSort32(): FPSort
    public fun mkFPSortDouble(): FPSort
    public fun mkFPSort64(): FPSort
    public fun mkFPSortQuadruple(): FPSort
    public fun mkFPSort128(): FPSort

    public fun mkFPNaN(sort: FPSort): FPNum
    public fun mkFPInf(sort: FPSort, negative: Boolean): FPNum
    public fun mkFPZero(sort: FPSort, negative: Boolean): FPNum
    public fun mkFPNumeral(value: Float, sort: FPSort): FPNum
    public fun mkFPNumeral(value: Double, sort: FPSort): FPNum
    public fun mkFPNumeral(value: Int, sort: FPSort): FPNum
    public fun mkFPNumeral(sign: Boolean, significand: Int, exponent: Int, sort: FPSort): FPNum
    public fun mkFPNumeral(sign: Boolean, significand: Long, exponent: Long, sort: FPSort): FPNum
    public fun mkFP(value: Float, sort: FPSort): FPNum
    public fun mkFP(value: Double, sort: FPSort): FPNum
    public fun mkFP(value: Int, sort: FPSort): FPNum
    public fun mkFP(sign: Boolean, significand: Int, exponent: Int, sort: FPSort): FPNum
    public fun mkFP(sign: Boolean, significand: Long, exponent: Long, sort: FPSort): FPNum

    public fun mkFPAbs(expr: Expr<FPSort>): FPExpr
    public fun mkFPNeg(expr: Expr<FPSort>): FPExpr
    public fun mkFPAdd(
        rm: Expr<FPRMSort>,
        left: Expr<FPSort>,
        right: Expr<FPSort>
    ): FPExpr

    public fun mkFPSub(
        rm: Expr<FPRMSort>,
        left: Expr<FPSort>,
        right: Expr<FPSort>
    ): FPExpr

    public fun mkFPMul(
        rm: Expr<FPRMSort>,
        left: Expr<FPSort>,
        right: Expr<FPSort>
    ): FPExpr

    public fun mkFPDiv(
        rm: Expr<FPRMSort>,
        left: Expr<FPSort>,
        right: Expr<FPSort>
    ): FPExpr

    public fun mkFPFMA(
        rm: Expr<FPRMSort>,
        t1: Expr<FPSort>,
        t2: Expr<FPSort>,
        t3: Expr<FPSort>
    ): FPExpr

    public fun mkFPSqrt(rm: Expr<FPRMSort>, expr: Expr<FPSort>): FPExpr
    public fun mkFPRem(left: Expr<FPSort>, right: Expr<FPSort>): FPExpr
    public fun mkFPRoundToIntegral(rm: Expr<FPRMSort>, expr: Expr<FPSort>): FPExpr
    public fun mkFPMin(left: Expr<FPSort>, right: Expr<FPSort>): FPExpr
    public fun mkFPMax(left: Expr<FPSort>, right: Expr<FPSort>): FPExpr

    public fun mkFPLEq(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr
    public fun mkFPLt(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr
    public fun mkFPGEq(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr
    public fun mkFPGt(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr
    public fun mkFPEq(left: Expr<FPSort>, right: Expr<FPSort>): BoolExpr

    public fun mkFPIsNormal(expr: Expr<FPSort>): BoolExpr
    public fun mkFPIsSubnormal(expr: Expr<FPSort>): BoolExpr
    public fun mkFPIsZero(expr: Expr<FPSort>): BoolExpr
    public fun mkFPIsInfinite(expr: Expr<FPSort>): BoolExpr
    public fun mkFPIsNaN(expr: Expr<FPSort>): BoolExpr
    public fun mkFPIsNegative(expr: Expr<FPSort>): BoolExpr
    public fun mkFPIsPositive(expr: Expr<FPSort>): BoolExpr

    public fun mkFP(
        sign: Expr<BitVecSort>,
        exponent: Expr<BitVecSort>,
        significand: Expr<BitVecSort>
    ): FPExpr

    public fun mkFPToFP(bv: Expr<BitVecSort>, sort: FPSort): FPExpr
    public fun mkFPToFP(rm: Expr<FPRMSort>, expr: FPExpr, sort: FPSort): FPExpr
    public fun mkFPToFP(rm: Expr<FPRMSort>, expr: RealExpr, sort: FPSort): FPExpr

    public fun mkFPToFP(
        rm: Expr<FPRMSort>,
        expr: Expr<BitVecSort>,
        sort: FPSort,
        isSigned: Boolean
    ): FPExpr

    public fun mkFPToFP(sort: FPSort, rm: Expr<FPRMSort>, expr: Expr<FPSort>): FPExpr

    public fun mkFPToBV(
        rm: Expr<FPRMSort>,
        expr: Expr<FPSort>,
        size: Int,
        isSigned: Boolean
    ): BitVecExpr

    public fun mkFPToReal(expr: Expr<FPSort>): RealExpr
    public fun mkFPToIEEEBV(expr: Expr<FPSort>): BitVecExpr

    public fun mkFPToFP(
        rm: Expr<FPRMSort>,
        sgn: Expr<IntSort>,
        exp: Expr<RealSort>,
        sort: FPSort
    ): BitVecExpr

    // Linear order
    public fun <R : Sort> mkLinearOrder(sort: R, index: Int): FuncDecl<BoolSort>
    public fun <R : Sort> mkPartialOrder(sort: R, index: Int): FuncDecl<BoolSort>

    // Help
    public fun SimplifyHelp(): String
    public fun getSimplifyParameterDescriptions(): ParamDescriptions
    public fun updateParamValue(key: String, value: String)

    public override fun close()
}
public expect abstract class Z3Object

public expect open class Z3Exception : Exception

public expect class ASTVector : Z3Object

public expect open class Symbol : Z3Object
public expect class IntSymbol : Symbol
public expect class StringSymbol : Symbol

public expect open class Sort : AST {
    public override fun translate(otherContext: Context): Sort
}

public expect class BoolSort : Sort
public expect open class ArithSort : Sort
public expect class IntSort : ArithSort
public expect class RealSort : ArithSort

public expect class BitVecSort : Sort {
    public fun getSize(): Int
}

public expect class CharSort : Sort
public expect class SetSort<D : Sort> : Sort
public expect class SeqSort<R : Sort> : Sort
public expect class ReSort<R : Sort> : Sort
public expect open class ArraySort<D : Sort, R : Sort> : Sort
public expect class DatatypeSort<R> : Sort
public expect class UninterpretedSort : Sort
public expect class TupleSort : Sort
public expect class ListSort<R : Sort> : Sort
public expect class EnumSort<R> : Sort
public expect class FiniteDomainSort<R> : Sort
public expect class FPSort : Sort
public expect class FPRMSort : Sort
public expect class RelationSort : Sort

public expect class FuncDecl<R : Sort> : Z3Object

public expect class Lambda<R : Sort> : ArrayExpr<Sort, R> {
    public override fun translate(otherContext: Context): Lambda<R>
}

public expect class Quantifier : Expr<BoolSort> {
    public override fun translate(otherContext: Context): Quantifier
}

public expect class Constructor<R> : Z3Object
public expect class ConstructorList<R> : Z3Object
public expect class Pattern : Z3Object
public expect class Tactic : Z3Object
public expect class Probe : Z3Object
public expect class Goal : Z3Object
public expect class ApplyResult : Z3Object
public expect class Params : Z3Object
public expect class ParamDescriptions : Z3Object
public expect class Simplifier : Z3Object
public expect class Fixedpoint : Z3Object

public expect class Solver : Z3Object {
    public fun push()
    public fun pop()
    public fun pop(n: Int)
    public fun reset()
    public fun interrupt()
    public fun add(vararg constraints: Expr<BoolSort>)
    public fun check(): Status
    public fun check(vararg assumptions: Expr<BoolSort>): Status
    public fun getModel(): Model?
    public fun getProof(): Expr<*>?
    public fun getUnsatCore(): Array<BoolExpr>
    public fun getReasonUnknown(): String?
    public fun translate(newContext: Context): Solver
    public fun getStatistics(): Statistics
}

public expect class Model : Z3Object {
    public fun <R : Sort> getConstInterp(expr: Expr<R>): Expr<R>?
    public fun <R : Sort> getConstInterp(funcDecl: FuncDecl<R>): Expr<R>?
    public fun <R : Sort> getFuncInterp(funcDecl: FuncDecl<R>): FuncInterp<R>?
    public fun getConstDecls(): Array<FuncDecl<*>>
    public fun getFuncDecls(): Array<FuncDecl<*>>
    public fun getDecls(): Array<FuncDecl<*>>
    public fun <R : Sort> eval(expr: Expr<R>, complete: Boolean): Expr<R>
    public fun getSorts(): Array<out Sort>
    public fun <R : Sort> getSortUniverse(sort: R): Array<out Expr<R>>
}

public expect class Optimize : Z3Object {
    public fun Assert(vararg exprs: Expr<BoolSort>)
    public fun Add(vararg constraints: Expr<BoolSort>)
    public fun AssertSoft(constraint: Expr<BoolSort>, weight: Int, group: String): Handle<*>
    public fun AssertSoft(constraint: Expr<BoolSort>, weight: String, group: String): Handle<*>
    public fun Check(vararg assumptions: Expr<BoolSort>): Status
    public fun getModel(): Model?
    public fun Push()
    public fun Pop()
    public fun getUnsatCore(): Array<BoolExpr>
    public fun <R : Sort> MkMaximize(expr: Expr<R>): Handle<R>
    public fun <R : Sort> MkMinimize(expr: Expr<R>): Handle<R>
    public fun getAssertions(): Array<BoolExpr>
    public fun getObjectives(): Array<out Expr<*>>
    public fun getStatistics(): Statistics

    public class Handle<R : Sort> {
        public fun getLower(): Expr<R>
        public fun getUpper(): Expr<R>
        public fun getValue(): Expr<R>
    }
}

public expect class Statistics : Z3Object {
    public fun getKeys(): Array<String>
    public fun size(): Int
}

public expect operator fun Statistics.get(key: String): Number
public expect fun Statistics.getAsString(key: String): String

public expect class FuncInterp<R : Sort> : Z3Object {
    public class Entry<R : Sort> : Z3Object
}

public expect enum class AstPrintMode {
    Z3_PRINT_SMTLIB_FULL,
    Z3_PRINT_LOW_LEVEL,
    Z3_PRINT_SMTLIB2_COMPLIANT
}

public expect enum class Status {
    SATISFIABLE,
    UNSATISFIABLE,
    UNKNOWN
}
