# Exercise 8.21

**EXERCISE 8.21.** Using the fixed-point construction, show that there is a continuous and computable operator $\lambda a.\, a^{\S}$, such that if $a$ is a finitary projection of $U$, then

$$D_{a^{\S}} \cong (D_a)^{\S} \ .$$

## Tip summary

The tip asserts that the sharp of a finitary projection is again a finitary projection.

## Development

Develops the sharp construction and shows it yields a finitary projection.

**[Exercise821.lean](Exercise821.lean)**

@import "Exercise821.lean"

The tip then assembles those tools into Scott’s statement.

**[Exercise_8_21.lean](Exercise_8_21.lean)** — `exercise_8_21`

@import "Exercise_8_21.lean"
