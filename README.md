# z3kt

Kotlin/Multiplatform bindings and a Kotlin-ish DSL for [Z3](https://github.com/Z3Prover/z3).
The code is currently not on a public maven repository, but it does support `gradle publish` to mavenLocal.

## Samples

Tests showcasing some basic capabilities of the wrapper [are available](src/commonTest/kotlin/Tests.kt).

A basic example is such:

```kotlin
// z3 as a block that returns a value
val solved = z3 {
    val x by int // Create a new variable x

    // Solve for x given some constraints
    val model = solve {
        add(6 * x + 3 eq 21)
    }!! // (a null model means the model was unsatisfiable)

    model[x].toInt() // Calculate, convert, and return the value of x satisfying the conditions
}
```

The wrapper originates as a Java wrapper, so the Java-style way of interacting
with Z3 is provided.

```kotlin
// z3 in the format the Java library offers
val context = Context()

val x = context.mkIntConst("x")
val sixX = context.mkMul(x, context.mkInt(6))
val plusThree = context.mkAdd(sixX, context.mkInt(3))

val solver = context.mkSolver()
solver.add(context.mkEq(plusThree, context.mkInt(21)))
val status = solver.check()
if (status != Status.SATISFIABLE) error("unexpected")

val model = solver.getModel()
val manuallySolved = model.eval(x, true)
```
