package com.sschr15.z3kt.test

import com.sschr15.z3kt.*
import kotlin.math.absoluteValue
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotNull

class Tests {
    @Test
    fun `test basic solve`() {
        val (a, b, c) = z3 {
            val a by int
            val b by int
            val c by int

            val model = solve {
                add(a   + 2*b - c eq 4)
                add(a   +   b + c eq 3)
                add(2*a +   b + c eq 5)
            }

            assertNotNull(model, "Model was deemed unsatisfiable")

            Triple(model[a].toInt(), model[b].toInt(), model[c].toInt())
        }

        assertEquals(2, a)
        assertEquals(1, b)
        assertEquals(0, c)
    }

    @Test
    fun `test AoC 2022 day 15 part 2 solve`() {
        val testData = listOf(
            (2 to 18) to (-2 to 15),
            (9 to 16) to (10 to 16),
            (13 to 2) to (15 to 3),
            (12 to 14) to (10 to 16),
            (10 to 20) to (10 to 16),
            (14 to 17) to (10 to 16),
            (8 to 7) to (2 to 10),
            (2 to 0) to (2 to 10),
            (0 to 11) to (2 to 10),
            (20 to 14) to (25 to 17),
            (17 to 20) to (21 to 22),
            (16 to 7) to (15 to 3),
            (14 to 3) to (15 to 3),
            (20 to 1) to (15 to 3),
        )

        val result = z3 {
            val x by int
            val y by int

            val model = solve {
                add(x gte 0)
                add(y gte 0)
                add(x lte 20)
                add(y lte 20)

                for ((beacon, sensor) in testData) {
                    val (bx, by) = beacon
                    val (sx, sy) = sensor

                    add((bx - sx).absoluteValue + (by - sy).absoluteValue lt (x - bx).abs() + (y - by).abs())
                }
            }
            assertNotNull(model, "Model was deemed unsatisfiable")

            assertEquals(14, model[x].toInt())
            assertEquals(11, model[y].toInt())
        }
    }

    @Test
    fun `test error handling`() {
        assertFailsWith<Z3Exception> {
            z3 {
                val myInconspicuousSymbol = mkSymbol(-1)
            }
        }

        assertFailsWith<Z3Exception> {
            z3 {
                val definitelyNotNaN = mkReal(0, 0)
            }
        }
    }

    @Test
    fun `test java library format`() {
        val context = Context()
        val x = context.mkIntConst("x")
        val sixXPlusThree = context.mkAdd(context.mkMul(context.mkInt(6), x), context.mkInt(3))
        val sixXPlusThreeString = sixXPlusThree.toString()
        assertEquals("(+ (* 6 x) 3)", sixXPlusThreeString)

        val solver = context.mkSolver()
        solver.add(context.mkEq(sixXPlusThree, context.mkInt(21)))
        val status = solver.check()
        assertEquals(Status.SATISFIABLE, status)

        val model = solver.getModel()!!
        val xValue = model.eval(x, true)
        assertEquals(3, xValue.toInt())
    }
}
