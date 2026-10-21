# Proposition 6.12

The subdomain relationship implies a mapping relationship between the domains.

**PROPOSITION 6.12.** If $D \triangleleft E$, then there exists a projection pair of approximable mappings:

$$
i : D \to E \quad \text{and} \quad j : E \to D
$$

where $j \circ i = I_D$ and $i \circ j \subseteq I_E$, which are determined as element-wise functions by these equations:

$$
i(x) = \{Y \in E \mid \exists X \in x.\, X \subseteq Y\},
$$

and

$$
j(y) = y \cap D,
$$

for all $x \in |D|$ and $y \in |E|$. $\square$

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Proposition612.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/ProjectionPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/ProjectionPair.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/inj.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/inj_comp_proj_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/inj_comp_proj_le.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/inj_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/inj_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/proj.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/proj_comp_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/proj_comp_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/proj_rel.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/proj_rel.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/projectionPair.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/projectionPair.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/toElementMap_inj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/toElementMap_inj.lean)
- [NeighbourhoodSystems/DomainEquations/Proposition612/toElementMap_proj.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Proposition612/toElementMap_proj.lean)
