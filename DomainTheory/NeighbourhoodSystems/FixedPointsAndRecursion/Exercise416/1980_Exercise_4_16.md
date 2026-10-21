# Exercise 4.16

**EXERCISE 4.16.** (For fixed-point nuts). Show that a monotone function as in 4.15 has an "optimal" fixed point in the sense that it is the greatest fixed point <u>below</u> all the maximal fixed points and at the same time it is the largest fixed point consistent with all other fixed points. *Consistency* for sets of elements means having a common upper bound. (Hint: Follow these steps:

(1) Show that any non-empty set $S$ of fixed points has a largest fixed point <u>below</u> by using the formula

$$
f(\bigcap S) \sqsubseteq \bigcap S
$$

and finding the least fixed point over $\bigcap S$.

(2) Letting $a$ be the fixed point of (1) constructed from the set of maximal fixed points, remark that $a$ is consistent with any other fixed point $x = f(x)$, since $x$ can be extended to a maximal one. Suppose $b$ is consistent with all fixed points, then $b \sqsubseteq y$ if $y$ is maximal. (Why?).)

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/f_sInf_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/f_sInf_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_consistent.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_consistent.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_le.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_le_sInf.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise416/optimalFix_le_sInf.lean)
