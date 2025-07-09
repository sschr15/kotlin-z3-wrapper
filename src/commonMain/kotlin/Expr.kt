package com.sschr15.z3kt

public typealias ExprArray = Array<out Expr<*>>

public expect open class AST : Z3Object {
    public fun isApp(): Boolean
    public fun isVar(): Boolean
    public fun isQuantifier(): Boolean
    public fun isSort(): Boolean
    public fun isFuncDecl(): Boolean
    public fun isExpr(): Boolean
    public open fun translate(otherContext: Context): AST
}

public expect open class Expr<S : Sort> : AST {
    public fun simplify(): Expr<S>
    public fun simplify(params: Params): Expr<S>
    public fun getFuncDecl(): FuncDecl<S>
    public fun getArgs(): ExprArray
    public fun update(args: ExprArray): Expr<S>
    public fun substitute(from: ExprArray, to: ExprArray): Expr<S>
    public fun substitute(from: Expr<*>, to: Expr<*>): Expr<S>
    public fun substituteVars(substitutions: ExprArray): Expr<S>
    public override fun translate(otherContext: Context): Expr<S>

    public fun getSort(): S
    public fun getIndex(): Int

    public fun isNumeral(): Boolean
    public fun isWellSorted(): Boolean
    public fun isConst(): Boolean
    public fun isIntNum(): Boolean
    public fun isRatNum(): Boolean
    public fun isAlgebraicNumber(): Boolean
    public fun isBool(): Boolean
    public fun isTrue(): Boolean
    public fun isFalse(): Boolean
    public fun isEq(): Boolean
    public fun isDistinct(): Boolean
    public fun isITE(): Boolean
    public fun isAnd(): Boolean
    public fun isOr(): Boolean
    public fun isIff(): Boolean
    public fun isXor(): Boolean
    public fun isNot(): Boolean
    public fun isImplies(): Boolean
    public fun isInt(): Boolean
    public fun isReal(): Boolean
    public fun isArithmeticNumeral(): Boolean
    public fun isLE(): Boolean
    public fun isGE(): Boolean
    public fun isLT(): Boolean
    public fun isGT(): Boolean
    public fun isAdd(): Boolean
    public fun isMul(): Boolean
    public fun isSub(): Boolean
    public fun isUMinus(): Boolean
    public fun isDiv(): Boolean
    public fun isIDiv(): Boolean
    public fun isRemainder(): Boolean
    public fun isModulus(): Boolean
    public fun isIntToReal(): Boolean
    public fun isRealToInt(): Boolean
    public fun isRealIsInt(): Boolean
    public fun isArray(): Boolean
    public fun isStore(): Boolean
    public fun isSelect(): Boolean
    public fun isConstantArray(): Boolean
    public fun isDefaultArray(): Boolean
    public fun isArrayMap(): Boolean
    public fun isAsArray(): Boolean
    public fun isSetUnion(): Boolean
    public fun isSetIntersect(): Boolean
    public fun isSetDifference(): Boolean
    public fun isSetComplement(): Boolean
    public fun isSetSubset(): Boolean
    public fun isBV(): Boolean
    public fun isBVNumeral(): Boolean
    public fun isBVBitOne(): Boolean
    public fun isBVBitZero(): Boolean
    public fun isBVUMinus(): Boolean
    public fun isBVAdd(): Boolean
    public fun isBVSub(): Boolean
    public fun isBVMul(): Boolean
    public fun isBVSDiv(): Boolean
    public fun isBVUDiv(): Boolean
    public fun isBVSRem(): Boolean
    public fun isBVURem(): Boolean
    public fun isBVSMod(): Boolean
    public fun isBVULE(): Boolean
    public fun isBVSLE(): Boolean
    public fun isBVUGE(): Boolean
    public fun isBVSGE(): Boolean
    public fun isBVULT(): Boolean
    public fun isBVSLT(): Boolean
    public fun isBVUGT(): Boolean
    public fun isBVSGT(): Boolean
    public fun isBVAND(): Boolean
    public fun isBVOR(): Boolean
    public fun isBVNOT(): Boolean
    public fun isBVXOR(): Boolean
    public fun isBVNAND(): Boolean
    public fun isBVNOR(): Boolean
    public fun isBVXNOR(): Boolean
    public fun isBVConcat(): Boolean
    public fun isBVSignExtension(): Boolean
    public fun isBVZeroExtension(): Boolean
    public fun isBVExtract(): Boolean
    public fun isBVRepeat(): Boolean
    public fun isBVReduceOR(): Boolean
    public fun isBVReduceAND(): Boolean
    public fun isBVComp(): Boolean
    public fun isBVShiftLeft(): Boolean
    public fun isBVShiftRightLogical(): Boolean
    public fun isBVShiftRightArithmetic(): Boolean
    public fun isBVRotateLeft(): Boolean
    public fun isBVRotateRight(): Boolean
    public fun isBVRotateLeftExtended(): Boolean
    public fun isBVRotateRightExtended(): Boolean
    public fun isIntToBV(): Boolean
    public fun isBVToInt(): Boolean
    public fun isBVCarry(): Boolean
    public fun isBVXOR3(): Boolean
    public fun isLabel(): Boolean
    public fun isLabelLit(): Boolean
    public fun isString(): Boolean
    public fun isConcat(): Boolean

    public fun isOEQ(): Boolean
    public fun isProofTrue(): Boolean
    public fun isProofAsserted(): Boolean
    public fun isProofGoal(): Boolean
    public fun isProofModusPonens(): Boolean
    public fun isProofReflexivity(): Boolean
    public fun isProofSymmetry(): Boolean
    public fun isProofTransitivity(): Boolean
    public fun isProofTransitivityStar(): Boolean
    public fun isProofMonotonicity(): Boolean
    public fun isProofQuantIntro(): Boolean
    public fun isProofDistributivity(): Boolean
    public fun isProofAndElimination(): Boolean
    public fun isProofOrElimination(): Boolean
    public fun isProofRewrite(): Boolean
    public fun isProofRewriteStar(): Boolean
    public fun isProofPullQuant(): Boolean
    public fun isProofPushQuant(): Boolean
    public fun isProofElimUnusedVars(): Boolean
    public fun isProofDER(): Boolean
    public fun isProofQuantInst(): Boolean
    public fun isProofHypothesis(): Boolean
    public fun isProofLemma(): Boolean
    public fun isProofUnitResolution(): Boolean
    public fun isProofIFFTrue(): Boolean
    public fun isProofIFFFalse(): Boolean
    public fun isProofCommutativity(): Boolean
    public fun isProofDefAxiom(): Boolean
    public fun isProofDefIntro(): Boolean
    public fun isProofApplyDef(): Boolean
    public fun isProofIFFOEQ(): Boolean
    public fun isProofNNFPos(): Boolean
    public fun isProofNNFNeg(): Boolean
    public fun isProofSkolemize(): Boolean
    public fun isProofModusPonensOEQ(): Boolean
    public fun isProofTheoryLemma(): Boolean

    public fun isRelation(): Boolean
    public fun isRelationStore(): Boolean
    public fun isEmptyRelation(): Boolean
    public fun isIsEmptyRelation(): Boolean
    public fun isRelationalJoin(): Boolean
    public fun isRelationUnion(): Boolean
    public fun isRelationWiden(): Boolean
    public fun isRelationProject(): Boolean
    public fun isRelationFilter(): Boolean
    public fun isRelationNegationFilter(): Boolean
    public fun isRelationRename(): Boolean
    public fun isRelationComplement(): Boolean
    public fun isRelationSelect(): Boolean
    public fun isRelationClone(): Boolean
    public fun isFiniteDomain(): Boolean
    public fun isFiniteDomainLT(): Boolean
}

public expect class BoolExpr : Expr<BoolSort>
public expect open class ArithExpr<S : ArithSort> : Expr<S>
public expect open class IntExpr : ArithExpr<IntSort>
public expect open class RealExpr : ArithExpr<RealSort>
public expect open class BitVecExpr : Expr<BitVecSort>
public expect open class ArrayExpr<D : Sort, R : Sort> : Expr<ArraySort<D, R>>
public expect class SeqExpr<R : Sort> : Expr<SeqSort<R>>
public expect class ReExpr<R : Sort> : Expr<ReSort<R>>
public expect open class FPExpr : Expr<FPSort>
public expect open class FPRMExpr : Expr<FPRMSort>

public expect class IntNum : IntExpr
public expect class RatNum : RealExpr
public expect class BitVecNum : BitVecExpr
public expect class FPNum : FPExpr
public expect class FPRMNum : FPRMExpr
