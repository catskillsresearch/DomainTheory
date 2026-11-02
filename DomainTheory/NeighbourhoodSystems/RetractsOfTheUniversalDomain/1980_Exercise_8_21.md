# Exercise 8.21
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_21.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_21.lean)**

@import "Exercise_8_21.lean"

**EXERCISE 8.21.** Using the fixed-point construction, show that there is a continuous and computable operator $\lambda a.\, a^{\S}$, such that if $a$ is a finitary projection of $U$, then

$$D_{a^{\S}} \cong (D_a)^{\S} \ .$$

## Tip summary

The tip asserts that the sharp of a finitary projection is again a finitary projection.

## Development

Develops the sharp construction and shows it yields a finitary projection.

 — `aSharp` projection/computability companions and Ex 8.25 closing

The tip then assembles those tools into Scott’s statement.

 — `exercise_8_21`

