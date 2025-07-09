@file:Suppress("NOTHING_TO_INLINE")

package com.sschr15.z3kt

public inline fun Optimize.add(vararg constraints: Expr<BoolSort>): Unit = Add(*constraints)
public inline fun Optimize.assert(vararg constraints: Expr<BoolSort>): Unit = Assert(*constraints)
//public inline fun Optimize.assertAndTrack(constraint: Expr<BoolSort>, p: Expr<BoolSort>): Unit = AssertAndTrack(constraint, p)
public inline fun Optimize.assertSoft(constraint: Expr<BoolSort>, weight: Int, group: String): Optimize.Handle<*> = AssertSoft(constraint, weight, group)
public inline fun Optimize.assertSoft(constraint: Expr<BoolSort>, weight: String, group: String): Optimize.Handle<*> = AssertSoft(constraint, weight, group)

public inline fun <T : Sort> Optimize.maximize(expr: Expr<T>): Optimize.Handle<T> = MkMaximize(expr)
public inline fun <T : Sort> Optimize.minimize(expr: Expr<T>): Optimize.Handle<T> = MkMinimize(expr)

public inline fun Optimize.push(): Unit = Push()
public inline fun Optimize.pop(): Unit = Pop()
public inline fun Optimize.pop(n: Int): Unit = repeat(n) { pop() }
