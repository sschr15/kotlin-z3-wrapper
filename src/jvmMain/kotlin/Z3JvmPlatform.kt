package com.sschr15.z3kt

public actual typealias Context = com.microsoft.z3.Context
public actual typealias Z3Object = com.microsoft.z3.Z3Object
public actual typealias Z3Exception = com.microsoft.z3.Z3Exception

public actual typealias AST = com.microsoft.z3.AST

public actual typealias Symbol = com.microsoft.z3.Symbol
public actual typealias IntSymbol = com.microsoft.z3.IntSymbol
public actual typealias StringSymbol = com.microsoft.z3.StringSymbol

public actual typealias Sort = com.microsoft.z3.Sort
public actual typealias BoolSort = com.microsoft.z3.BoolSort
public actual typealias ArithSort = com.microsoft.z3.ArithSort
public actual typealias IntSort = com.microsoft.z3.IntSort
public actual typealias RealSort = com.microsoft.z3.RealSort
public actual typealias BitVecSort = com.microsoft.z3.BitVecSort
public actual typealias CharSort = com.microsoft.z3.CharSort
public actual typealias SetSort<D> = com.microsoft.z3.SetSort<D>
public actual typealias SeqSort<R> = com.microsoft.z3.SeqSort<R>
public actual typealias ReSort<R> = com.microsoft.z3.ReSort<R>
public actual typealias ArraySort<D, R> = com.microsoft.z3.ArraySort<D, R>
public actual typealias DatatypeSort<R> = com.microsoft.z3.DatatypeSort<R>
public actual typealias UninterpretedSort = com.microsoft.z3.UninterpretedSort
public actual typealias TupleSort = com.microsoft.z3.TupleSort
public actual typealias ListSort<R> = com.microsoft.z3.ListSort<R>
public actual typealias EnumSort<R> = com.microsoft.z3.EnumSort<R>
public actual typealias FiniteDomainSort<R> = com.microsoft.z3.FiniteDomainSort<R>
public actual typealias FPSort = com.microsoft.z3.FPSort
public actual typealias FPRMSort = com.microsoft.z3.FPRMSort

public actual typealias Expr<S> = com.microsoft.z3.Expr<S>
public actual typealias BoolExpr = com.microsoft.z3.BoolExpr
public actual typealias ArithExpr<S> = com.microsoft.z3.ArithExpr<S>
public actual typealias IntExpr = com.microsoft.z3.IntExpr
public actual typealias RealExpr = com.microsoft.z3.RealExpr
public actual typealias BitVecExpr = com.microsoft.z3.BitVecExpr
public actual typealias ArrayExpr<D, R> = com.microsoft.z3.ArrayExpr<D, R>
public actual typealias SeqExpr<R> = com.microsoft.z3.SeqExpr<R>
public actual typealias ReExpr<R> = com.microsoft.z3.ReExpr<R>
public actual typealias FPExpr = com.microsoft.z3.FPExpr
public actual typealias FPRMExpr = com.microsoft.z3.FPRMExpr
public actual typealias RelationSort = com.microsoft.z3.RelationSort

public actual typealias IntNum = com.microsoft.z3.IntNum
public actual typealias RatNum = com.microsoft.z3.RatNum
public actual typealias BitVecNum = com.microsoft.z3.BitVecNum
public actual typealias FPNum = com.microsoft.z3.FPNum
public actual typealias FPRMNum = com.microsoft.z3.FPRMNum

public actual typealias FuncDecl<R> = com.microsoft.z3.FuncDecl<R>
public actual typealias Lambda<R> = com.microsoft.z3.Lambda<R>

public actual typealias Constructor<R> = com.microsoft.z3.Constructor<R>
public actual typealias ConstructorList<R> = com.microsoft.z3.ConstructorList<R>
public actual typealias Pattern = com.microsoft.z3.Pattern
public actual typealias Quantifier = com.microsoft.z3.Quantifier
public actual typealias Tactic = com.microsoft.z3.Tactic
public actual typealias Probe = com.microsoft.z3.Probe
public actual typealias Goal = com.microsoft.z3.Goal
public actual typealias ApplyResult = com.microsoft.z3.ApplyResult
public actual typealias Params = com.microsoft.z3.Params
public actual typealias ParamDescriptions = com.microsoft.z3.ParamDescrs
public actual typealias Statistics = com.microsoft.z3.Statistics
public actual typealias Solver = com.microsoft.z3.Solver
public actual typealias Model = com.microsoft.z3.Model
public actual typealias Simplifier = com.microsoft.z3.Simplifier
public actual typealias Fixedpoint = com.microsoft.z3.Fixedpoint
public actual typealias Optimize = com.microsoft.z3.Optimize

public actual typealias FuncInterp<R> = com.microsoft.z3.FuncInterp<R>

public actual typealias AstPrintMode = com.microsoft.z3.enumerations.Z3_ast_print_mode
public actual typealias Status = com.microsoft.z3.Status

public actual operator fun Statistics.get(key: String): Number {
    val entry = get(key)
    return when {
        entry.isDouble -> entry.doubleValue
        entry.isUInt -> entry.uIntValue
        else -> throw Z3Exception("Unknown statistical entry type")
    }
}

public actual fun Statistics.getAsString(key: String): String = get(key).valueString
