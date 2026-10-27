# Exercise 8.24

**EXERCISE 8.24.** Suppose $S$ and $T$ are two (binary-argument) constructs on domains that can be made into computable operators on projections of the universal domain. Show that we can therefore find a pair of effectively presented domains such that
$$
D \cong S(D, E) \quad \text{and} \quad E \cong T(D, E).
$$

## Tip summary

The tip asserts that the coupled solutions `a★`, `b★` are finitary projections.

## Development

Solves the coupled domain equations with finitary projections `a★`, `b★`.

**[CoupledFixedPoints.lean](CoupledFixedPoints.lean)**

@import "CoupledFixedPoints.lean"

The tip then assembles those tools into Scott’s statement.

**[Exercise_8_24.lean](Exercise_8_24.lean)** — `exercise_8_24`

@import "Exercise_8_24.lean"
