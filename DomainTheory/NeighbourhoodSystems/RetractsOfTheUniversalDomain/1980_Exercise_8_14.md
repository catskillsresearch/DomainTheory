# Exercise 8.14

**EXERCISE 8.14.** A retraction $a : D \to D$ is called a *closure operator* iff $I_D \sqsubseteq a$. On a domain like $P\mathbf{N}$, give some examples of closure operators. (Hint: Close up a set of integers under addition. Is this continuous on $P\mathbf{N}$?) Prove in general for any closure $a : D \to D$ that the fixed-point set of $a$ is always a finitary domain. (Hint: Show that the fixed-point set is closed under intersections and directed unions.) What are the finite elements of the fixed-point set?

## Tip summary

The tip states that the fixed-point set of any closure operator is a finitary domain.

## Development

Defines closure operators and shows `Fix(a)` is a finitary domain.

**[ClosureOperatorDomain.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/ClosureOperatorDomain.lean)**

@import "ClosureOperatorDomain.lean"
**[NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_14.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise_8_14.lean)**

@import "Exercise_8_14.lean"
The tip then assembles those tools into Scott’s statement.

 — `exercise_8_14`

@import "Exercise_8_14.lean"
