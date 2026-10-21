# Exercise 4.17

**EXERCISE 4.17.** (For algebraists). Suppose $\langle S, 1, \cdot \rangle$ is a semi-group with unit (sometimes called a monoid). Remark that $PS$ is a domain. For $a, b \in S$, what is the least $x \in PS$ such that

$$
x = \{1\} \cup \{a, b\} \cup x \cdot x,
$$

where in general for $x, y \subseteq S$

$$
x \cdot y = \{ t \cdot u \mid t \in x \text{ and } u \in y \}?
$$

Need the fixed point be unique?

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417.lean](../Exercise417.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F.lean](F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F_monotone.lean](F_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F_one_one_singleton.lean](F_one_one_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/F_univ.lean](F_univ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/a_mem_F.lean](a_mem_F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/b_mem_F.lean](b_mem_F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/base_subset_F.lean](base_subset_F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/fixedPoint_not_unique.lean](fixedPoint_not_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/leastSolution_eq.lean](leastSolution_eq.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/lfpSet_eq_closure.lean](lfpSet_eq_closure.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/one_mem_F.lean](one_mem_F.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/preFixSubmonoid.lean](preFixSubmonoid.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise417/self_mul_subset_F.lean](self_mul_subset_F.lean)
