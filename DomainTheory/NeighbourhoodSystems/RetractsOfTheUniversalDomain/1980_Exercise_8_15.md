# Exercise 8.15

**EXERCISE 8.15.** Give a direct proof that the domain $\{X \mid X \triangleleft D\}$ is effectively presented if $D$ is. (Hint: The finite elements of the domain correspond exactly to the finite systems $X \triangleleft D$.) In the case of $D = \mathcal{U}$, show that the computable elements of the domain correspond exactly to the effectively presented domains (up to effective isomorphism).

## Tip summary

The tip states that if `D` is effectively given then so is (a presentation of) the domain of its subsystems.

## Development

Constructs an effectively given presentation of the domain of subsystems.

**[SubsystemDomain.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/SubsystemDomain.lean)**

@import "SubsystemDomain.lean"

The tip then assembles those tools into Scott’s statement.

**[Exercise_8_15.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_15.lean)** — `exercise_8_15`

@import "Exercise_8_15.lean"
