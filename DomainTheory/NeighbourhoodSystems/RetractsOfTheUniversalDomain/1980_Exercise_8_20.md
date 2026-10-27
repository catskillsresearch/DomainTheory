# Exercise 8.20

**EXERCISE 8.20.** For any system we know $D \trianglelefteq D + D$, but what about

$$D \trianglelefteq D \times D \quad \text{and} \quad D \trianglelefteq D \to D \ ?$$

Would these projections be computable if $D$ is effectively given? Are there more than one projection pair in each case?

## Tip summary

The tip asserts `D ⊴ D×D` and `D ⊴ D→D` for every domain `D`.

## Development

Proves the unconditional self-embeddings `D ⊴ D×D` and `D ⊴ D→D`.

**[Exercise820.lean](Exercise820.lean)**

@import "Exercise820.lean"

The tip then assembles those tools into Scott’s statement.

**[Exercise_8_20.lean](Exercise_8_20.lean)** — `exercise_8_20`

@import "Exercise_8_20.lean"
