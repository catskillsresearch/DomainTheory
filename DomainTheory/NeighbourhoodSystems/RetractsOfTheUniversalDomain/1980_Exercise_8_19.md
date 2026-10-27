# Exercise 8.19

**EXERCISE 8.19.** Suppose we know both

$$T \quad \text{and} \quad E \to E \trianglelefteq E \ .$$

Does it follow that $E + E$ and $E \times E \trianglelefteq E$?

## Tip summary

The tip asserts closure of `⊴` under sum and product under Scott’s hypotheses.

## Development

Closes `⊴` under sum and product given a terminal object and a function-space retract.

**[Exercise819.lean](Exercise819.lean)**

@import "Exercise819.lean"

The tip then assembles those tools into Scott’s statement.

**[Exercise_8_19.lean](Exercise_8_19.lean)** — `exercise_8_19`

@import "Exercise_8_19.lean"
