# Exercise 4.13

**EXERCISE 4.13.** The proof of 4.1 uses the integers, whereas the proof of 4.6 uses 4.1. There is a hint of circularity here! It can be eliminated by the following steps:

(1) If a domain $D$ has an element $a$ where, for $f : D \to D$, the relation $f(a) \sqsubseteq a$ holds, then the least fixed point can be defined by

$$
\mathrm{fix}(f) = \bigcap \{ x \in |D| \mid f(x) \sqsubseteq x \}.
$$

Note that $\mathrm{fix}(f) \sqsubseteq a$. (Hint: Remark that by 1.17 the formula gives a well-defined element. Call the element $b$. Prove that $f(b) \sqsubseteq b$ by showing that $f(b) \sqsubseteq x$ whenever $f(x) \sqsubseteq x$. Then note that $f(f(b)) \sqsubseteq f(b)$ so that $b \sqsubseteq f(b)$ also. Conclude $b = \mathrm{fix}(f)$ as least fixed point.)

(2) Remark that this proof uses only the monotonicity property of $f : |D| \to |D|$. Remark, too, that (1) can always be applied to power-set domains $PA$ for any set $A$.

(3) Review the proof of 4.6 and establish by a fixed-point method that for any structured set $\langle Z, z, \cdot \rangle$ there is a unique function $s : \mathbf{N} \to Z$ such that

(i) $s(0) = z$;

(ii) $s(n^+) = s(n)^\cdot$, for $n \in \mathbf{N}$.

(4) Employ (3) for the proof of 4.1 by identifying $\langle \mathbf{N}, 0, {}^+ \rangle$.

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/exists_unique_nat_rec.lean](exists_unique_nat_rec.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_le_preFix.lean](monoFix_le_preFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_le.lean](monoFix_le.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_least.lean](monoFix_least.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_preFix.lean](monoFix_preFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix_isFixed.lean](monoFix_isFixed.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/nat_iterate_unique.lean](nat_iterate_unique.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413.lean](../Exercise413.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/preFix.lean](preFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/mem_preFix.lean](mem_preFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/monoFix.lean](monoFix.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise413/Basic.lean](Basic.lean)
