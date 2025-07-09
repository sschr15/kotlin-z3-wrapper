package com.sschr15.z3kt

import kotlinx.cinterop.CPointer
import kotlinx.cinterop.toKString
import lib.z3.*

internal fun <S : Sort> Expr(native: Z3_ast, context: Context): Expr<S> {
    val kind = Z3_get_ast_kind(context.native, native)
    if (kind == Z3_QUANTIFIER_AST) return Quantifier(native, context) as Expr<S>
    val sort = Z3_get_sort_kind(context.native, Z3_get_sort(context.native, native))
    return ((if (Z3_is_numeral_ast(context.native, native)) when (sort) {
        Z3_INT_SORT -> IntNum(native, context)
        Z3_REAL_SORT -> RatNum(native, context)
        Z3_BV_SORT -> BitVecNum(native, context)
        Z3_FLOATING_POINT_SORT -> FPNum(native, context)
        Z3_ROUNDING_MODE_SORT -> FPRMNum(native, context)
        else -> null
    } else null) ?: when (sort) {
        Z3_BOOL_SORT -> BoolExpr(native, context)
        Z3_INT_SORT -> IntExpr(native, context)
        Z3_REAL_SORT -> RealExpr(native, context)
        Z3_BV_SORT -> BitVecExpr(native, context)
        Z3_FLOATING_POINT_SORT -> FPExpr(native, context)
        Z3_ROUNDING_MODE_SORT -> FPRMExpr(native, context)
        Z3_ARRAY_SORT -> ArrayExpr<Sort, Sort>(native, context)
        Z3_SEQ_SORT -> SeqExpr<Sort>(native, context)
        Z3_RE_SORT -> ReExpr<Sort>(native, context)
        else -> Expr(context, native) // Call real base constructor if all others fail
    }) as Expr<S>
}

private val exprTypes = setOf(
    Z3_APP_AST,
    Z3_NUMERAL_AST,
    Z3_QUANTIFIER_AST,
    Z3_VAR_AST,
)

public actual open class AST(internal val context: Context, private val native: Z3_ast) : Z3Object() {
    public actual fun isApp(): Boolean = Z3_get_ast_kind(context.native, native) == Z3_APP_AST
    public actual fun isVar(): Boolean = Z3_get_ast_kind(context.native, native) == Z3_VAR_AST
    public actual fun isQuantifier(): Boolean = Z3_get_ast_kind(context.native, native) == Z3_QUANTIFIER_AST
    public actual fun isSort(): Boolean = Z3_get_ast_kind(context.native, native) == Z3_SORT_AST
    public actual fun isFuncDecl(): Boolean = Z3_get_ast_kind(context.native, native) == Z3_FUNC_DECL_AST
    public actual fun isExpr(): Boolean = Z3_get_ast_kind(context.native, native) in exprTypes

    protected open val selfNative: CPointer<*> = native

    public actual open fun translate(otherContext: Context): AST = if (context == otherContext) {
        this
    } else when (Z3_get_ast_kind(context.native, native)) {
        Z3_FUNC_DECL_AST -> FuncDecl<Sort>(Z3_translate(context.native, native, otherContext.native)!! as Z3_func_decl, otherContext)
        Z3_QUANTIFIER_AST -> Quantifier(Z3_translate(context.native, native, otherContext.native)!!, otherContext)
        Z3_SORT_AST -> Sort(Z3_translate(context.native, native, otherContext.native)!! as Z3_sort, otherContext)
        Z3_APP_AST, Z3_NUMERAL_AST, Z3_VAR_AST -> Expr<Sort>(Z3_translate(context.native, native, otherContext.native)!!, otherContext)
        else -> error("Unknown AST type")
    }

    public override fun toString(): String = Z3_ast_to_string(context.native, native)!!.toKString()
}

public actual open class Expr<S : Sort>(context: Context, internal val native: Z3_ast) : AST(context, native) {
    private val app by lazy { Z3_to_app(context.native, native) }
    private fun nativeFunc() = Z3_get_app_decl(context.native, app)!!

    public actual fun simplify(): Expr<S> = Expr(Z3_simplify(context.native, native)!!, context)
    public actual fun simplify(params: Params): Expr<S> = Expr(Z3_simplify_ex(context.native, native, params.native)!!, context)
    public actual fun getFuncDecl(): FuncDecl<S> = FuncDecl(Z3_get_app_decl(context.native, app)!!, context)

    public actual fun getArgs(): ExprArray = Array(Z3_get_app_num_args(context.native, app).toInt()) {
        Expr<Sort>(Z3_get_app_arg(context.native, app, it.toUInt())!!, context)
    }

    public actual fun update(args: ExprArray): Expr<S> = Expr(Z3_update_term(context.native, native, args.size.toUInt(), args.native)!!, context)
    public actual fun substitute(from: ExprArray, to: ExprArray): Expr<S> = Expr(Z3_substitute(context.native, native, from.size.toUInt(), from.native, to.native)!!, context)
    public actual fun substitute(from: Expr<*>, to: Expr<*>): Expr<S> = substitute(arrayOf(from), arrayOf(to))
    public actual fun substituteVars(substitutions: ExprArray): Expr<S> = Expr(Z3_substitute_vars(context.native, native, substitutions.size.toUInt(), substitutions.native)!!, context)
    public actual override fun translate(otherContext: Context): Expr<S> = Expr(Z3_translate(context.native, native, otherContext.native)!!, otherContext)

    public actual fun getSort(): S = Sort(Z3_get_sort(context.native, native)!!, context) as S
    public actual fun getIndex(): Int = Z3_get_index_value(context.native, native).toInt()

    public actual fun isNumeral(): Boolean = Z3_is_numeral_ast(context.native, native)
    public actual fun isWellSorted(): Boolean = Z3_is_well_sorted(context.native, native)
    public actual fun isIntNum(): Boolean = isNumeral() && isInt()
    public actual fun isRatNum(): Boolean = isNumeral() && isReal()
    public actual fun isAlgebraicNumber(): Boolean = Z3_is_algebraic_number(context.native, native)
    public actual fun isBool(): Boolean = isExpr() && Z3_is_eq_sort(context.native, context.getBoolSort().native, Z3_get_sort(context.native, native))
    public actual fun isInt(): Boolean = Z3_get_sort_kind(context.native, Z3_get_sort(context.native, native)) == Z3_INT_SORT
    public actual fun isReal(): Boolean = Z3_get_sort_kind(context.native, Z3_get_sort(context.native, native)) == Z3_REAL_SORT
    public actual fun isArray(): Boolean = isApp() && Z3_get_sort_kind(context.native, Z3_get_sort(context.native, native)) == Z3_ARRAY_SORT
    public actual fun isBV(): Boolean = Z3_get_sort_kind(context.native, Z3_get_sort(context.native, native)) == Z3_BV_SORT

    public actual fun isConst(): Boolean = isApp() && Z3_get_app_num_args(context.native, app).toInt() == 0 && Z3_get_domain_size(context.native, nativeFunc()) == 0u
    public actual fun isString(): Boolean = isApp() && Z3_is_string(context.native, native)
    public actual fun isRelation(): Boolean = isApp() && Z3_get_sort_kind(context.native, Z3_get_sort(context.native, native)) == Z3_RELATION_SORT

    public actual fun isTrue(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_TRUE
    public actual fun isFalse(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_FALSE
    public actual fun isEq(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_EQ
    public actual fun isDistinct(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_DISTINCT
    public actual fun isITE(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ITE
    public actual fun isAnd(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_AND
    public actual fun isOr(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_OR
    public actual fun isIff(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_IFF
    public actual fun isXor(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_XOR
    public actual fun isNot(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_NOT
    public actual fun isImplies(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_IMPLIES
    public actual fun isArithmeticNumeral(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ANUM
    public actual fun isLE(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_LE
    public actual fun isGE(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_GE
    public actual fun isLT(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_LT
    public actual fun isGT(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_GT
    public actual fun isAdd(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ADD
    public actual fun isMul(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_MUL
    public actual fun isSub(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SUB
    public actual fun isUMinus(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_UMINUS
    public actual fun isDiv(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_DIV
    public actual fun isIDiv(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_IDIV
    public actual fun isRemainder(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_REM
    public actual fun isModulus(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_MOD
    public actual fun isIntToReal(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_TO_REAL
    public actual fun isRealToInt(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_TO_INT
    public actual fun isRealIsInt(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_IS_INT
    public actual fun isStore(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_STORE
    public actual fun isSelect(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SELECT
    public actual fun isConstantArray(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_CONST_ARRAY
    public actual fun isDefaultArray(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ARRAY_DEFAULT
    public actual fun isArrayMap(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ARRAY_MAP
    public actual fun isAsArray(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_AS_ARRAY
    public actual fun isSetUnion(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SET_UNION
    public actual fun isSetIntersect(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SET_INTERSECT
    public actual fun isSetDifference(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SET_DIFFERENCE
    public actual fun isSetComplement(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SET_COMPLEMENT
    public actual fun isSetSubset(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SET_SUBSET
    public actual fun isBVNumeral(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BNUM
    public actual fun isBVBitOne(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BIT1
    public actual fun isBVBitZero(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BIT0
    public actual fun isBVUMinus(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BNEG
    public actual fun isBVAdd(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BADD
    public actual fun isBVSub(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BSUB
    public actual fun isBVMul(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BMUL
    public actual fun isBVSDiv(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BSDIV
    public actual fun isBVUDiv(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BUDIV
    public actual fun isBVSRem(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BSREM
    public actual fun isBVURem(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BUREM
    public actual fun isBVSMod(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BSMOD
    public actual fun isBVULE(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ULEQ
    public actual fun isBVSLE(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SLEQ
    public actual fun isBVUGE(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_UGEQ
    public actual fun isBVSGE(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SGEQ
    public actual fun isBVULT(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ULT
    public actual fun isBVSLT(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SLT
    public actual fun isBVUGT(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_UGT
    public actual fun isBVSGT(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SGT
    public actual fun isBVAND(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BAND
    public actual fun isBVOR(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BOR
    public actual fun isBVNOT(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BNOT
    public actual fun isBVXOR(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BXOR
    public actual fun isBVNAND(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BNAND
    public actual fun isBVNOR(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BNOR
    public actual fun isBVXNOR(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BXNOR
    public actual fun isBVConcat(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_CONCAT
    public actual fun isBVSignExtension(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SIGN_EXT
    public actual fun isBVZeroExtension(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ZERO_EXT
    public actual fun isBVExtract(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_EXTRACT
    public actual fun isBVRepeat(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_REPEAT
    public actual fun isBVReduceOR(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BREDOR
    public actual fun isBVReduceAND(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BREDAND
    public actual fun isBVComp(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BCOMP
    public actual fun isBVShiftLeft(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BSHL
    public actual fun isBVShiftRightLogical(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BLSHR
    public actual fun isBVShiftRightArithmetic(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BASHR
    public actual fun isBVRotateLeft(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ROTATE_LEFT
    public actual fun isBVRotateRight(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_ROTATE_RIGHT
    public actual fun isBVRotateLeftExtended(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_EXT_ROTATE_LEFT
    public actual fun isBVRotateRightExtended(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_EXT_ROTATE_RIGHT
    public actual fun isIntToBV(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_INT2BV
    public actual fun isBVToInt(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_BV2INT
    public actual fun isBVCarry(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_CARRY
    public actual fun isBVXOR3(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_XOR3
    public actual fun isLabel(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_LABEL
    public actual fun isLabelLit(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_LABEL_LIT
    public actual fun isConcat(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_SEQ_CONCAT

    public actual fun isOEQ(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_OEQ
    public actual fun isProofTrue(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_TRUE
    public actual fun isProofAsserted(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_ASSERTED
    public actual fun isProofGoal(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_GOAL
    public actual fun isProofModusPonens(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_MODUS_PONENS
    public actual fun isProofReflexivity(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_REFLEXIVITY
    public actual fun isProofSymmetry(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_SYMMETRY
    public actual fun isProofTransitivity(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_TRANSITIVITY
    public actual fun isProofTransitivityStar(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_TRANSITIVITY_STAR
    public actual fun isProofMonotonicity(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_MONOTONICITY
    public actual fun isProofQuantIntro(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_QUANT_INTRO
    public actual fun isProofDistributivity(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_DISTRIBUTIVITY
    public actual fun isProofAndElimination(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_AND_ELIM
    public actual fun isProofOrElimination(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_NOT_OR_ELIM
    public actual fun isProofRewrite(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_REWRITE
    public actual fun isProofRewriteStar(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_REWRITE_STAR
    public actual fun isProofPullQuant(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_PULL_QUANT
    public actual fun isProofPushQuant(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_PUSH_QUANT
    public actual fun isProofElimUnusedVars(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_ELIM_UNUSED_VARS
    public actual fun isProofDER(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_DER
    public actual fun isProofQuantInst(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_QUANT_INST
    public actual fun isProofHypothesis(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_HYPOTHESIS
    public actual fun isProofLemma(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_LEMMA
    public actual fun isProofUnitResolution(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_UNIT_RESOLUTION
    public actual fun isProofIFFTrue(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_IFF_TRUE
    public actual fun isProofIFFFalse(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_IFF_FALSE
    public actual fun isProofCommutativity(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_COMMUTATIVITY
    public actual fun isProofDefAxiom(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_DEF_AXIOM
    public actual fun isProofDefIntro(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_DEF_INTRO
    public actual fun isProofApplyDef(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_APPLY_DEF
    public actual fun isProofIFFOEQ(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_IFF_OEQ
    public actual fun isProofNNFPos(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_NNF_POS
    public actual fun isProofNNFNeg(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_NNF_NEG
    public actual fun isProofSkolemize(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_SKOLEMIZE
    public actual fun isProofModusPonensOEQ(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_MODUS_PONENS_OEQ
    public actual fun isProofTheoryLemma(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_PR_TH_LEMMA

    public actual fun isRelationStore(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_STORE
    public actual fun isEmptyRelation(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_EMPTY
    public actual fun isIsEmptyRelation(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_IS_EMPTY
    public actual fun isRelationalJoin(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_JOIN
    public actual fun isRelationUnion(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_UNION
    public actual fun isRelationWiden(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_WIDEN
    public actual fun isRelationProject(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_PROJECT
    public actual fun isRelationFilter(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_FILTER
    public actual fun isRelationNegationFilter(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_NEGATION_FILTER
    public actual fun isRelationRename(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_RENAME
    public actual fun isRelationComplement(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_COMPLEMENT
    public actual fun isRelationSelect(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_SELECT
    public actual fun isRelationClone(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_RA_CLONE
    public actual fun isFiniteDomain(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_FD_CONSTANT
    public actual fun isFiniteDomainLT(): Boolean = isApp() && Z3_get_decl_kind(context.native, nativeFunc()) == Z3_OP_FD_LT
}
