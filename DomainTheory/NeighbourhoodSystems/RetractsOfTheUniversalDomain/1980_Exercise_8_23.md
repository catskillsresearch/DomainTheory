# Exercise 8.23

**EXERCISE 8.23.** Suppose a construct $T$ on domains can be made into a computable operator $t : (U \to U) \to (U \to U)$ so that whenever $a : U \to U$ is a finitary projection, then so is $t(a)$ and

$$D_{t(a)} \cong T(D_a) \ .$$

Does it follow that $\|t\| = \mathrm{fix}(t)$ is such that

$$D_{\|t\|} \cong T(D_{\|t\|})$$

<!-- page 149 -->

really is the initial solution of the domain equation with respect to projections? Since $t$ is computable, will this solution be effectively given?

## Tip summary

The tip asserts that `fixOp t` is a finitary projection whenever `t` preserves them.

## Development

Defines `fixOp` and proves it is finitary when the transformer preserves finitary projections.

**[FixOp.lean](FixOp.lean)**

@import "FixOp.lean"

The tip then assembles those tools into Scott’s statement.

**[Exercise_8_23.lean](Exercise_8_23.lean)** — `exercise_8_23`

@import "Exercise_8_23.lean"
