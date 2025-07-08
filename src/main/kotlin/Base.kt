@file:Suppress("NOTHING_TO_INLINE")

package com.sschr15.z3kt

import com.microsoft.z3.*
import kotlin.contracts.InvocationKind
import kotlin.contracts.contract
import kotlin.io.path.Path
import kotlin.io.path.absolutePathString
import kotlin.io.path.outputStream

@PublishedApi
internal var initialized: Boolean = false

/**
 * Run a block of code with a z3 context.
 */
public inline fun <R> z3(block: Context.() -> R): R {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }

    if (!initialized) try {
        val os = System.getProperty("os.name").lowercase()
        val arch = System.getProperty("os.arch").lowercase()

        val fileExtension = when {
            os.contains("win") -> "dll"
            os.contains("mac") -> "dylib"
            os.contains("nix") || os.contains("nux") -> "so"
            else -> error("Unsupported OS: $os")
        }

        val archName = when {
            "amd64" in arch || "x86_64" in arch -> "x64"
            "arm64" in arch -> "arm64"
            "x86" in arch || "i386" in arch -> "x86"
            else -> error("Unsupported architecture: $arch")
        }

        if (fileExtension == "dll" && archName == "arm64") error("Z3 has no prebuilt DLL for arm64")
        if (archName == "x86" && fileExtension != "dll") error("Z3 provides only a DLL for x86")

        val libName = "libz3.$fileExtension"
        val javaLibName = "libz3java.$fileExtension"

        val libPath = "natives/$archName/$libName"
        val javaLibPath = "natives/$archName/$javaLibName"

        val lib = Class.forName("com.sschr15.z3kt.BaseKt").getResourceAsStream("/$libPath") ?: error("Failed to find native library: $libPath")
        val javaLib = Class.forName("com.sschr15.z3kt.BaseKt").getResourceAsStream("/$javaLibPath") ?: error("Failed to find native library: $javaLibPath")

        val libOut = Path("libz3.$fileExtension")
        val javaLibOut = Path("libz3java.$fileExtension")

        lib.use { libOut.outputStream().use(it::copyTo) }
        javaLib.use { javaLibOut.outputStream().use(it::copyTo) }

        System.load(libOut.absolutePathString())
        System.load(javaLibOut.absolutePathString())

        System.setProperty("z3.skipLibraryLoad", "true")

        initialized = true
    } catch (e: Exception) {
        System.err.println("Failed to extract native libraries: ${e.message}")
        System.err.println("Try installing Z3 through a package manager if it fails to load through the Z3 library.")
    }

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
            Status.SATISFIABLE -> solver.model
            Status.UNSATISFIABLE -> null
            Status.UNKNOWN -> error("Solver failed to determine satisfiability")
            null -> error("Solver returned null status on satisfiability check")
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
            Status.SATISFIABLE -> opt.model
            Status.UNSATISFIABLE -> null
            Status.UNKNOWN -> error("Optimizer failed to determine satisfiability")
            null -> error("Optimizer returned null status on satisfiability check")
        }
    }
}

/**
 * Evaluate the expression in the model.
 */
public inline operator fun <T : Sort> Model.get(expr: Expr<T>): Expr<T> =
    eval(expr, true)
