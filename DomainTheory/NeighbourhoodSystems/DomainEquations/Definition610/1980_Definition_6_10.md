# Definition 6.10

The final question we have to answer is why in our category the minimal $D$ exist. The reason is that the functors $T$ that we have in mind possess further continuity properties on domains. This is conveniently expressed in terms of a notion of "subdomain".

**DEFINITION 6.10.** For two neighbourhood systems $D$ and $E$ we write

$$
D \triangleleft E
$$

to mean that these are neighbourhood systems over the same set of tokens $\Delta$ and not only is $D \subseteq E$ but whenever $X, Y \in D$ and $X \cap Y \in E$, then $X \cap Y \in D$. $\square$

For the subdomain relation $D \triangleleft E$ to hold, $D$ has to be a smaller family of neighbourhoods, but the notion of consistency in $D$ also has to be the same as in $E$. Note that if $D_0 \triangleleft E$ and $D_1 \triangleleft E$ then
$$
D_0 \triangleleft D_1 \text{ iff } D_0 \subseteq D_1.
$$

It is also easy to prove that the union of a directed family of subdomains of $E$ is again a subdomain. As a consequence of this remark we have:

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Definition610.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/Basic/notation2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/Basic/notation2.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/Subsystem.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/Subsystem.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/_root_u2eDomainTheoryu2eNeighborhoodu2eNeighborhoodSystemu2eext.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/_root_u2eDomainTheoryu2eNeighborhoodu2eNeighborhoodSystemu2eext.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/antisymm.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/antisymm.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/refl.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/refl.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/subsystem_iff_subset_of_common.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/subsystem_iff_subset_of_common.lean)
- [NeighbourhoodSystems/DomainEquations/Definition610/trans.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Definition610/trans.lean)
