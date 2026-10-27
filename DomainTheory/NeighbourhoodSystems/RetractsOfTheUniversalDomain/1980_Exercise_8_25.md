# Exercise 8.25

**EXERCISE 8.25.** The problem is to find non-trivial solutions to the domain equation
$$
(\spadesuit) \qquad D \cong D \to D.
$$
Show that the "obvious" solution by retracts is of no use because
$$
1 \to 1 = 1
$$
for projections. Change the method as follows. Show first
$$
U^\infty \times U^\infty \cong U^\infty.
$$
Next solve
$$
D \cong D \to U^\infty
$$
and remark that $U \triangleleft D$; so $D$ is universal and non-trivial. Finally prove $(\spadesuit)$ for this $D$. (Hint: First show
$$
D \times D \cong D,
$$
and then show $D$ satisfies $(\spadesuit)$.) Is this $D$ effectively given?

## Tip summary

The tip asserts existence of a non-trivial domain isomorphic to its function space and containing `U`.

## Development

Rational-interval coding used by effective presentations.

**[QPairCodes.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/QPairCodes.lean)**

@import "QPairCodes.lean"
Builds a non-trivial reflexive domain $D \cong D\to D$ containing `U`.

**[ReflexiveDomain.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/ReflexiveDomain.lean)**

@import "ReflexiveDomain.lean"
The tip then assembles those tools into Scott’s statement.

 — `exercise_8_25`

@import "Exercise_8_25.lean"
