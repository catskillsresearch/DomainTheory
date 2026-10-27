# Exercise 8.16

**EXERCISE 8.16.** For finitary projections $a : E \to E$, write

$$D_a = \{X \in E \mid X \sqsubseteq a X\}$$

(cf. 8.5.). Show that for any two such projections $a, b : E \to E$ we have

$$a \sqsubseteq b \quad \text{iff} \quad D_a \triangleleft D_b.$$

(This fills in the gap at the end of the proof of 8.6.) Also finish off the proof of 8.8 by showing that if $E$ is effectively given and $a : E \to E$ is computable, then $D_a$ is effectively given.

## Tip summary

The tip packages the order correspondence for finitary projections with the effectivity of their fixed neighbourhoods.

## Development

Matches the order of finitary projections with subdomain order and records effectivity of `D_a`.

**[FixedNbhdFinitaryOrder.lean](FixedNbhdFinitaryOrder.lean)**

@import "FixedNbhdFinitaryOrder.lean"

The tip then assembles those tools into Scott’s statement.

**[Exercise_8_16.lean](Exercise_8_16.lean)** — `exercise_8_16`

@import "Exercise_8_16.lean"
