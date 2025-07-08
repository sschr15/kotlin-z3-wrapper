package com.sschr15.z3kt

import com.microsoft.z3.*
import kotlin.properties.PropertyDelegateProvider
import kotlin.properties.ReadOnlyProperty
import kotlin.reflect.KProperty

public class ExprDelegateProvider<T : Expr<*>> internal constructor(
    private val context: Context,
    private val getter: Context.(String) -> T
) : PropertyDelegateProvider<Any?, ExprDelegateProvider.Delegate<T>> {
    public class Delegate<T : Expr<*>>(private val value: T) : ReadOnlyProperty<Any?, T> {
        override fun getValue(thisRef: Any?, property: KProperty<*>): T = value
    }

    override fun provideDelegate(thisRef: Any?, property: KProperty<*>): Delegate<T> {
        val name = property.name
        return Delegate(context.getter(name))
    }
}

public val Context.bool: ExprDelegateProvider<BoolExpr>
    get() = ExprDelegateProvider(this) { mkBoolConst(it) }

public val Context.int: ExprDelegateProvider<IntExpr>
    get() = ExprDelegateProvider(this) { mkIntConst(it) }

public val Context.real: ExprDelegateProvider<RealExpr>
    get() = ExprDelegateProvider(this) { mkRealConst(it) }

public fun Context.bitVec(size: Int): ExprDelegateProvider<BitVecExpr>
    = ExprDelegateProvider(this) { mkBVConst(it, size) }
