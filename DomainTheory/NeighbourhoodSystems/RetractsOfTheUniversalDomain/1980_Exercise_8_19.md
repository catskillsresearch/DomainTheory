# Exercise 8.19

**EXERCISE 8.19.** Suppose we know both

$$T \quad \text{and} \quad E \to E \trianglelefteq E \ .$$

Does it follow that $E + E$ and $E \times E \trianglelefteq E$?

## Tip summary

The tip asserts closure of $\trianglelefteq$ under sum and product under Scott’s hypotheses.

## Development

Closes $\trianglelefteq$ under sum and product given a terminal object and a function-space retract.

**[SumProdRetracts.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/SumProdRetracts.lean)**

@import "SumProdRetracts.lean"
The tip then assembles those tools into Scott’s statement.

 — `exercise_8_19`

@import "Exercise_8_19.lean"
