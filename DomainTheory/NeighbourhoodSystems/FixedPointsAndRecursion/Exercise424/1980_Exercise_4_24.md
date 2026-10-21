# Exercise 4.24

**EXERCISE 4.24.** (For set theorists). Let $f : A \to B$ and $g : B \to A$ be one-one functions (into, not necessarily onto!) Prove the Schroeder - Bernstein theorem to the effect that there exists a one-one correspondence $h : A \leftrightarrow B$. (Hint: (Suggested by A. Tarski). By the fixed-point theorem find $X \subseteq A$ where

$$
X = (A - g(B)) \cup g(f(X)),
$$

where $f(X) =$ the image of the set $X$ under the function $f$. Define $h \subseteq A \times B$ as a union of two restrictions:

$$
h = f \upharpoonright X \cup g^{-1} \upharpoonright (A - X).
$$

A picture helps.)

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/g_f_mem_of_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/g_f_mem_of_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/g_sbFun_not_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/g_sbFun_not_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/mem_range_of_not_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/mem_range_of_not_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_injective.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_injective.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_surjective.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbFun_surjective.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbOp.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbOp.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbOp_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbOp_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbSet.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbSet.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbSet_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/sbSet_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/schroeder_bernstein.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/schroeder_bernstein.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/schroeder_bernstein_equiv.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise424/schroeder_bernstein_equiv.lean)
