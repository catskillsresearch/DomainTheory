# Exercise 5.15

**EXERCISE 5.15.** (For algebraists.) We can regard $\langle \{0,1\}^*, \Lambda, \cdot \rangle$ as the free semigroup on two generators $0$ and $1$. The powerset $P\{0,1\}^*$ is taken as a domain as in Exercise 4.17. For "words" $e \in \{0,1\}^*$ define

$$
e^* = \{\Lambda, e, e^2, e^3, \ldots, e^n, \ldots\}.
$$

Show that the least fixed point of

$$
z = \{e\} \cdot z \cup \{e'\}
$$

in $P\{0,1\}^*$ is $z = e^* \cdot \{e'\}$.

Show further (as suggested by David Park) that the least solution of

$$
\begin{aligned}
x &= a \cdot x \cup b \cdot y \cup c, \\
y &= b \cdot x \cup a \cdot y \cup d
\end{aligned}
$$

has

$$
x = (a \cup b \cdot a^* \cdot b)^* \cdot (c \cup b \cdot a^* \cdot d),
$$

where the $\{\cdot\}$ has been dropped off $\{a\}$, $\{b\}$ etc., and where the $^*$-notation has been extended to the whole domain, so that $z^* = \Lambda \cup z^* \cdot z$.

(Hint: Apply 5.3.)

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/G.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/G.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/arden.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/arden.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow_succ.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow_succ.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow_zero.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/kpow_zero.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_kpow_singleton.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_kpow_singleton.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_star.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_star.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_star_singleton.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/mem_star_singleton.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkA.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkA.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkC.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkC.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkX.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkX.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkX_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkX_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkY.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkY.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkY_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/parkY_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/park_least.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/park_least.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/park_solves.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/park_solves.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/part1.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/part1.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/part1_freeMonoid.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/part1_freeMonoid.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/smul_assoc.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/smul_assoc.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/smul_union.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/smul_union.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_eq.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_eq.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_mul_isFixed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_mul_isFixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_mul_subset_prefixed.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/star_mul_subset_prefixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/sunion_mul.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise515/sunion_mul.lean)
