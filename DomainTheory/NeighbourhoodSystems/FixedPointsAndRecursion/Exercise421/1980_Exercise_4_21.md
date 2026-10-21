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

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421.lean](../Exercise421.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso.lean](addIso.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_apply.lean](addIso_apply.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_succ.lean](addIso_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/addIso_zero.lean](addIso_zero.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp.lean](leOp.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_monotone.lean](leOp_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leOp_unique.lean](leOp_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel.lean](leRel.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/leRel_isFixed.lean](leRel_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mem_fixedPoint_iff.lean](mem_fixedPoint_iff.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp.lean](mulOp.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_lfp_eq_multiples.lean](mulOp_lfp_eq_multiples.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/mulOp_monotone.lean](mulOp_monotone.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/succImage.lean](succImage.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet.lean](upSet.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_succ.lean](upSet_succ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_unique.lean](upSet_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise421/upSet_zero.lean](upSet_zero.lean)
