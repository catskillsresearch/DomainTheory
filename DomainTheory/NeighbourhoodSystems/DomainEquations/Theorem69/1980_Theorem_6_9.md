# Theorem 6.9

**THEOREM 6.9.** If the functor $T$ is continuous on maps and if $D \cong T(D)$, so in particular $D$ is a $T$-algebra, then for any $T$-algebra $k : T(E) \to E$ there is a homomorphism $h : D \to E$.

*Proof:* Let $i : T(D) \to D$ make $D$ a $T$-algebra, where $j : D \to T(D)$ is the inverse so that $i$ is an isomorphism of domains. Suppose that $k : T(E) \to E$ is any $T$-algebra. A homomorphism $h : D \to E$ would satisfy

$$
h \circ i = k \circ T(h).
$$

Rewrite this equation as

$$
h = k \circ T(h) \circ j.
$$

In the domain of strict maps $(D \to E)$ this is a fixed-point equation for an approximable map

$$
\lambda h.\, k \circ T(h) \circ j
$$

by our assumption on $T$. Thus, the desired homomorphism exists. $\square$

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Theorem69.lean](../Theorem69.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/comp_mono_gen.lean](comp_mono_gen.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOp.lean](homOp.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOpComp.lean](homOpComp.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOpComp_mono.lean](homOpComp_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOp_apply_filter.lean](homOp_apply_filter.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/homOp_rel.lean](homOp_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/isStrict_comp.lean](isStrict_comp.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/isStrict_of_comp_eq_id.lean](isStrict_of_comp_eq_id.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/nonempty_algHom_of_continuousOnMaps.lean](nonempty_algHom_of_continuousOnMaps.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/toStrictFilter_mono.lean](toStrictFilter_mono.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/toStrictFilter_toStrictMap.lean](toStrictFilter_toStrictMap.lean)
- [NeighbourhoodSystems/DomainEquations/Theorem69/toStrictMap_mono.lean](toStrictMap_mono.lean)
