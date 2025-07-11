@file:Suppress("FunctionName")

package com.sschr15.z3kt

import kotlinx.cinterop.*
import lib.z3.*

public actual class Solver(internal val native: Z3_solver, context: Context) : Z3Object(context) {
    public actual fun push(): Unit = Z3_solver_push(context.native, native)
    public actual fun pop(): Unit = Z3_solver_pop(context.native, native, 1u)
    public actual fun pop(n: Int): Unit = Z3_solver_pop(context.native, native, n.toUInt())
    public actual fun reset(): Unit = Z3_solver_reset(context.native, native)
    public actual fun interrupt(): Unit = Z3_solver_interrupt(context.native, native)

    public actual fun add(vararg constraints: Expr<BoolSort>) {
        for (constraint in constraints) {
            Z3_solver_assert(context.native, native, constraint.native)
        }
    }

    public actual fun check(): Status = when (Z3_solver_check(context.native, native)) {
        -1 -> Status.UNSATISFIABLE
        0 -> Status.UNKNOWN
        1 -> Status.SATISFIABLE
        else -> error("Unexpected solver check result")
    }

    public actual fun check(vararg assumptions: Expr<BoolSort>): Status =
        when (Z3_solver_check_assumptions(context.native, native, assumptions.size.toUInt(), assumptions.native)) {
            -1 -> Status.UNSATISFIABLE
            0 -> Status.UNKNOWN
            1 -> Status.SATISFIABLE
            else -> error("Unexpected solver check result")
        }

    public actual fun getModel(): Model? = Z3_solver_get_model(context.native, native)?.let { Model(it, context) }
    public actual fun getProof(): Expr<*>? = Z3_solver_get_proof(context.native, native)?.let { Expr<Sort>(it, context) }

    public actual fun getUnsatCore(): Array<BoolExpr> {
        val vector = Z3_solver_get_unsat_core(context.native, native) ?: return emptyArray()
        return Array(Z3_ast_vector_size(context.native, vector).toInt()) {
            BoolExpr(Z3_ast_vector_get(context.native, vector, it.toUInt())!!, context)
        }
    }

    public actual fun getReasonUnknown(): String? = Z3_solver_get_reason_unknown(context.native, native)?.toKString()
    public actual fun translate(newContext: Context): Solver = Solver(Z3_solver_translate(context.native, native, newContext.native)!!, newContext)
    public actual fun getStatistics(): Statistics = Statistics(Z3_solver_get_statistics(context.native, native)!!, context)

    override fun toString(): String = Z3_solver_to_string(context.native, native)!!.toKString()
}

public class ModelEvalFailedException : Z3Exception("Model evaluation failed")

public actual class Model(internal val native: Z3_model, context: Context) : Z3Object(context) {
    public actual fun <R : Sort> getConstInterp(expr: Expr<R>): Expr<R>? = getConstInterp(expr.getFuncDecl())
    public actual fun <R : Sort> getConstInterp(funcDecl: FuncDecl<R>): Expr<R>? = Z3_model_get_const_interp(context.native, native, funcDecl.native)?.let { Expr(it, context) }
    public actual fun <R : Sort> getFuncInterp(funcDecl: FuncDecl<R>): FuncInterp<R>? = Z3_model_get_func_interp(context.native, native, funcDecl.native)?.let { FuncInterp(it, context) }

    public actual fun getConstDecls(): Array<FuncDecl<*>> = Array(Z3_model_get_num_consts(context.native, native).toInt()) {
        FuncDecl<Sort>(Z3_model_get_const_decl(context.native, native, it.toUInt())!!, context)
    }

    public actual fun getFuncDecls(): Array<FuncDecl<*>> = Array(Z3_model_get_num_funcs(context.native, native).toInt()) {
        FuncDecl<Sort>(Z3_model_get_func_decl(context.native, native, it.toUInt())!!, context)
    }

    public actual fun getDecls(): Array<FuncDecl<*>> = getFuncDecls() + getConstDecls()

    public actual fun <R : Sort> eval(expr: Expr<R>, complete: Boolean): Expr<R> = memScoped {
        val ast = allocArray<Z3_astVar>(1)
        if (!Z3_model_eval(context.native, native, expr.native, complete, ast)) {
            throw ModelEvalFailedException()
        }
        return Expr(ast.pointed.value!!, context)
    }

    public actual fun getSorts(): Array<out Sort> = Array(Z3_model_get_num_sorts(context.native, native).toInt()) {
        Sort(Z3_model_get_sort(context.native, native, it.toUInt())!!, context)
    }

    public actual fun <R : Sort> getSortUniverse(sort: R): Array<out Expr<R>> {
        val vec = Z3_model_get_sort_universe(context.native, native, sort.native as Z3_sort) ?: return emptyArray()
        return Array(Z3_ast_vector_size(context.native, vec).toInt()) {
            Expr(Z3_ast_vector_get(context.native, vec, it.toUInt())!!, context)
        }
    }
}

public actual class Optimize(internal val native: Z3_optimize, context: Context) : Z3Object(context) {
    public actual fun Assert(vararg exprs: Expr<BoolSort>) {
        for (expr in exprs) {
            Z3_optimize_assert(context.native, native, expr.native)
        }
    }

    public actual fun Add(vararg constraints: Expr<BoolSort>): Unit = Assert(*constraints)
    public actual fun AssertSoft(constraint: Expr<BoolSort>, weight: String, group: String): Handle<*> =
        Handle<Sort>(this, Z3_optimize_assert_soft(context.native, native, constraint.native, weight, context.mkSymbol(group).native))

    public actual fun AssertSoft(constraint: Expr<BoolSort>, weight: Int, group: String): Handle<*> =
        AssertSoft(constraint, weight.toString(), group)

    public actual fun Check(vararg assumptions: Expr<BoolSort>): Status = when (Z3_optimize_check(context.native, native, assumptions.size.toUInt(), assumptions.native)) {
        -1 -> Status.UNSATISFIABLE
        0 -> Status.UNKNOWN
        1 -> Status.SATISFIABLE
        else -> error("Unexpected optimize check result")
    }

    public actual fun getModel(): Model? = Z3_optimize_get_model(context.native, native)?.let { Model(it, context) }
    public actual fun Push(): Unit = Z3_optimize_push(context.native, native)
    public actual fun Pop(): Unit = Z3_optimize_pop(context.native, native)

    public actual fun getUnsatCore(): Array<BoolExpr> {
        val vector = Z3_optimize_get_unsat_core(context.native, native) ?: return emptyArray()
        return Array(Z3_ast_vector_size(context.native, vector).toInt()) {
            BoolExpr(Z3_ast_vector_get(context.native, vector, it.toUInt())!!, context)
        }
    }

    public actual fun <R : Sort> MkMaximize(expr: Expr<R>): Handle<R> = Handle(this, Z3_optimize_maximize(context.native, native, expr.native))
    public actual fun <R : Sort> MkMinimize(expr: Expr<R>): Optimize.Handle<R> = Handle(this, Z3_optimize_minimize(context.native, native, expr.native))

    public actual fun getAssertions(): Array<BoolExpr> {
        val vector = Z3_optimize_get_assertions(context.native, native) ?: return emptyArray()
        return Array(Z3_ast_vector_size(context.native, vector).toInt()) {
            BoolExpr(Z3_ast_vector_get(context.native, vector, it.toUInt())!!, context)
        }
    }

    public actual fun getObjectives(): Array<out Expr<*>> {
        val vector = Z3_optimize_get_objectives(context.native, native) ?: return emptyArray()
        return Array(Z3_ast_vector_size(context.native, vector).toInt()) {
            Expr<Sort>(Z3_ast_vector_get(context.native, vector, it.toUInt())!!, context)
        }
    }

    public actual fun getStatistics(): Statistics = Statistics(Z3_optimize_get_statistics(context.native, native)!!, context)
    override fun toString(): String = Z3_optimize_to_string(context.native, native)!!.toKString()

    public actual class Handle<R : Sort>(internal val optimize: Optimize, internal val index: UInt) {
        public actual fun getLower(): Expr<R> = Expr(Z3_optimize_get_lower(optimize.context.native, optimize.native, index)!!, optimize.context)
        public actual fun getUpper(): Expr<R> = Expr(Z3_optimize_get_upper(optimize.context.native, optimize.native, index)!!, optimize.context)
        public actual fun getValue(): Expr<R> = getLower()
        override fun toString(): String = getValue().toString()
    }
}

public actual class Statistics(internal val native: Z3_stats, context: Context) : Z3Object(context) {
    internal val cache = getKeys().mapIndexed { i, s -> s to i.toUInt() }.toMap()

    public actual fun getKeys(): Array<String> = Array(Z3_stats_size(context.native, native).toInt()) {
        Z3_stats_get_key(context.native, native, it.toUInt())!!.toKString()
    }

    public actual fun size(): Int = Z3_stats_size(context.native, native).toInt()
    override fun toString(): String = Z3_stats_to_string(context.native, native)!!.toKString()
}

public actual operator fun Statistics.get(key: String): Number {
    val index = cache[key] ?: throw NoSuchElementException(key)
    return when {
        Z3_stats_is_uint(context.native, native, index) -> Z3_stats_get_uint_value(context.native, native, index).toInt()
        Z3_stats_is_double(context.native, native, index) -> Z3_stats_get_double_value(context.native, native, index)
        else -> error("Unexpected type when searching $key")
    }
}

public actual fun Statistics.getAsString(key: String): String = this[key].toString()
