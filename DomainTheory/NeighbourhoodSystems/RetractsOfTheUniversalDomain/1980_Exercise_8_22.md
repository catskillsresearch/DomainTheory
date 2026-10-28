# Exercise 8.22

**EXERCISE 8.22.** Which of the two relations hold:

$$B \trianglelefteq C \quad \text{or} \quad C \trianglelefteq B \ ?$$

Or do they both hold? In general if we use domain equations

$$D = T(D) + S(D) \ , \quad \text{and}$$

$$E = T(E) \ ,$$

will $E \trianglelefteq D$ hold? What projections do you see in the examples in 6.2?

## Tip summary

The tip asserts the concrete embedding relation between Scott’s examples `C` and `B`.

## Development

Compares Scott’s concrete examples `B` and `C`.

**[ExampleC_le_B.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/ExampleC_le_B.lean)**

@import "ExampleC_le_B.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_22.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_22.lean)**

@import "Exercise_8_22.lean"
The tip then assembles those tools into Scott’s statement.

 — `exercise_8_22`

@import "Exercise_8_22.lean"
