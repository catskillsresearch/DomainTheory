# Example 2.4

**EXAMPLE 2.4.** Let us briefly describe an approximable mapping $g : B \to B$. Informally, $g$ can be said to "read a sequence from left to right and eliminate the first consecutive run of 1's while copying all the other digits as read." We will have

$$
g(0^n 1^k 0 x) = 0^{n+1} x
$$

provided $k > 0$. (Here $1^k$ means a string of 1's of length $k$.) However, if $1^\infty$ is the infinite sequences of 1's, then

$$
\begin{aligned}
g(1^\infty) &= \perp, \text{ and} \\
g(0^n 1^\infty) &= 0^n.
\end{aligned}
$$

This example is instructive, since it shows that a non-trivial mapping can transform a total element into a partial element. $\square$

Aside from our being able to define particular functions outright, we can combine functions in many different ways; the idea of composition is probably the most basic scheme of combination, and there is a technical name for a family of structures with mappings that can be so combined.

**Lean 4**

- [NeighbourhoodSystems/MappingsBetweenDomains/Example24.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/Basic.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/Basic.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/SatisfiesRunEquations.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/SatisfiesRunEquations.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/del.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/del.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/del_append.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/del_append.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/del_false.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/del_false.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/del_nil.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/del_nil.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/del_true.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/del_true.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/eq_runMap_of_satisfies.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/eq_runMap_of_satisfies.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/key.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/key.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_append.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_append.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_append_false.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_append_false.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_append_trueFalse.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_append_trueFalse.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_append_trueTrue.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_append_trueTrue.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_false.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_false.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_mono.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_mono.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_nil.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_nil.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_true.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_true.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_true_false.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_true_false.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_true_true.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/out_true_true.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap_rel_cone.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap_rel_cone.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap_satisfies.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap_satisfies.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap_toElementMap_mem.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap_toElementMap_mem.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap_toElementMap_sigmaElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/runMap_toElementMap_sigmaElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Example24/sigmaElt_runMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Example24/sigmaElt_runMap_toElementMap.lean)
