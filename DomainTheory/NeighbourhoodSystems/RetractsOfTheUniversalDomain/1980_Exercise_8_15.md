# Exercise 8.15

**EXERCISE 8.15.** Give a direct proof that the domain $\{X \mid X \triangleleft D\}$ is effectively presented if $D$ is. (Hint: The finite elements of the domain correspond exactly to the finite systems $X \triangleleft D$.) In the case of $D = \mathcal{U}$, show that the computable elements of the domain correspond exactly to the effectively presented domains (up to effective isomorphism).

## Tip summary

The tip states that if `D` is effectively given then so is (a presentation of) the domain of its subsystems.

## Development

Library tools: finitely generated subsystems and the reconstructed system `SubD`.

 — `finGen`, `finGenSys`, `SubD`

@import "finGen.lean"

 — `QBody`, `QFuel`, `TreeVal`, `Q'X`

@import "TreeVal.lean"

 — `Q2X`, `Q'xPresentation`

@import "TreeVal_more.lean"

Assembles those tools into the Exercise 8.15 development (order iso, presentations, U-case).

**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/finGen.lean](finGen.lean)**

@import "finGen.lean"
The tip then assembles those tools into Scott’s statement.

 — `exercise_8_15`

@import "Exercise_8_15.lean"
