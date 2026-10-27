# Exercise 8.11

**EXERCISE 8.11.** Let $\mathbb{Q}$ be the set of rational numbers and define a neighbourhood system by the equation

$$R = \{[0, r) \mid r \in \mathbb{Q} \text{ and } 0 < r \le 1\}.$$

Show that the following defines an approximable map $a : R \to R$:

$$[0, r) \ a \ [0, s) \quad \text{iff} \quad r < s \text{ or } r = s = 1.$$

Show in addition that $a$ is a projection where the fixed-point set of $a$ is in a one-one correspondence with the *real* numbers between 0 and 1 inclusive. (Hint: Recall Dedekind cuts and show $\subseteq$ matches $\le$.) Conclude that $a$ is *NOT* finitary. (Hint: Aside from $\bot$ there are no finite elements for $\{x \mid x = a(x)\}$.)

## Tip summary

The tip records that Scott’s map `a` on `R` is a projection and is not finitary.

## Development

Builds the Dedekind-cut system `R` and proves the projection `a` is not finitary.

**[DedekindCutProjection.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/DedekindCutProjection.lean)**

@import "DedekindCutProjection.lean"
The tip then assembles those tools into Scott’s statement.

 — `exercise_8_11`

@import "Exercise_8_11.lean"
