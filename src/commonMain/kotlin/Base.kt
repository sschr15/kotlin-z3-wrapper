@file:Suppress("NOTHING_TO_INLINE")

package com.sschr15.z3kt

import kotlin.contracts.InvocationKind
import kotlin.contracts.contract

@PublishedApi
internal expect fun initialize()

/**
 * Run a block of code with a z3 context.
 */
public inline fun <R> z3(block: Context.() -> R): R {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }

    initialize()

    return Context().block()
}

/**
 * Run the z3 solver with a block of code. If satisfiable, return the model. Otherwise, return null.
 */
public inline fun Context.solve(block: Solver.() -> Unit): Model? {
    contract { 
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }

    val solver = mkSolver()
    solver.block()
    return solver.check().let {
        when (it) {
            Status.SATISFIABLE -> solver.getModel()
            Status.UNSATISFIABLE -> null
            Status.UNKNOWN -> error("Solver failed to determine satisfiability")
            else -> error("Unexpected solver status: $it")
        }
    }
}

/**
 * Run the z3 optimizer with a block of code. If satisfiable, return the model. Otherwise, return null.
 */
public inline fun Context.optimize(vararg assumptions: Expr<BoolSort>, block: Optimize.() -> Unit): Model? {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }

    val opt = mkOptimize()
    opt.block()
    return opt.Check(*assumptions).let {
        when (it) {
            Status.SATISFIABLE -> opt.getModel()
            Status.UNSATISFIABLE -> null
            Status.UNKNOWN -> error("Optimizer failed to determine satisfiability")
            else -> error("Unexpected solver status: $it")
        }
    }
}

/**
 * Evaluate the expression in the model.
 */
public inline operator fun <T : Sort> Model.get(expr: Expr<T>): Expr<T> =
    eval(expr, true)
