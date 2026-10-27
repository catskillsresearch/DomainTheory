# Exercise 8.17

**EXERCISE 8.17.** Find explicitly (if possible) the projection pairs for $\mathcal{U} + \mathcal{U}$, $\mathcal{U} \times \mathcal{U}$, and $\mathcal{U} \to \mathcal{U}$ needed for 8.9. Are any of these domains isomorphic with $\mathcal{U}$? (The author does not know a really good construction for $\mathcal{U} \to \mathcal{U}$.) Find a universal domain $V \neq \mathcal{U}$.

<!-- page 148 -->

## Tip summary

The tip asserts universality of `V` together with the product/sum/function-space embeddings into `U`.

## Development

Proves `V` is universal and records the standard embeddings into `U`.

**[EmbeddingsIntoU.lean](EmbeddingsIntoU.lean)**

@import "EmbeddingsIntoU.lean"

The tip then assembles those tools into Scott’s statement.

**[Exercise_8_17.lean](Exercise_8_17.lean)** — `exercise_8_17`

@import "Exercise_8_17.lean"
