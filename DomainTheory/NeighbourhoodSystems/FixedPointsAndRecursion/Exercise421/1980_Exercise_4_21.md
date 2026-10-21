# Exercise 4.21

$$
\mathrm{fix}(f \circ g) = f(\mathrm{fix}(g \circ f)).
$$

**EXERCISE 4.21.** Show that the less-than-or-equal-to relation $\ell \subseteq \mathbf{N} \times \mathbf{N}$ is uniquely determined by the fixed point equation

$$
\ell = \{(n,n) \mid n \in \mathbf{N}\} \cup \{(n, m^+) \mid (n, m) \in \ell\}.
$$

Consider the structured set $\langle P\mathbf{N}, \mathbf{N}, {}^+ \rangle$ where, as before, $x^+ = \{n^+ \mid n \in x\}$.

What is the unique function $[\cdot] : \mathbf{N} \to P\mathbf{N}$ given by 4.13(3)? Prove that the structures $\langle \mathbf{N}, 0, {}^+ \rangle$ and $\langle [m], m, {}^+ \rangle$ are uniquely isomorphic for each $m \in \mathbf{N}$, and connect the isomorphism with ordinary addition of integers. Can the same be done for multiplication? (Hint: Consider the fixed-point equation

$$
n \cdot \mathbf{N} = \{0\} \cup \{n + m \mid m \in n \cdot \mathbf{N}\},
$$

where $n \in \mathbf{N}$ is fixed.)

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_apply.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_apply.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel_isFixed.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mem_fixedPoint_iff.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mem_fixedPoint_iff.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_lfp_eq_multiples.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_lfp_eq_multiples.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_monotone.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/succImage.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/succImage.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_succ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_unique.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_zero.lean)
