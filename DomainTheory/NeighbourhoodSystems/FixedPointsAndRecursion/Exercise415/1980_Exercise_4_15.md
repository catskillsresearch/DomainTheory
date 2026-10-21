# Exercise 4.15

**EXERCISE 4.15.** (For set theorists.) Let $f : |D| \to |D|$ be a monotone function on (the elements of) a domain. Show that $f$ has a *maximal* fixed point (i.e. a fixed point that cannot be extended to a larger fixed point). (Hint: By Zorn's Lemma consider a maximal chain

$$
C \subseteq \{ x \in |D| \mid x \sqsubseteq f(x) \},
$$

and use 2.11 to remark that $\bigsqcup C \in |D|$.) Now argue that $f$ has a <u>least</u> fixed point.

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415.lean](../Exercise415.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/chainUnion_le.lean](chainUnion_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/exists_least_fixedPoint.lean](exists_least_fixedPoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise415/exists_maximal_fixedPoint.lean](exists_maximal_fixedPoint.lean)
