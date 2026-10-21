# Exercise 2.13

**EXERCISE 2.13.** (For topologists.) Recall Exercise 1.22 where it was shown that any domain $|D|$ is a topological space. Prove from Exercise 2.9 that the functions $f : |D_0| \to |D_1|$ determined by approximable mappings are exactly *the continuous functions between these spaces.* (Hint: To prove continuity, remark that by 2.9

$$
f^{-1}[Y] = \bigcup \{ [X] \mid Y \in f(\uparrow X) \};
$$

hence, the inverse image of any open set is open. In the other direction, suppose that $f : |D_0| \to |D_1|$ is topologically continuous. Argue that for all $x \in |D_0|$ and all open subsets $U \subseteq |D_1|$ we have

$$
f(x) \in U \text{ iff } \exists X \in x.\ f(\uparrow X) \in U.
$$

This holds because an open subset of $|D_0|$ is always a union of basic open subsets of the form $[X']$ for $X \in D_0$ and because

$$
x = \bigcup \{ \uparrow X \mid X \in x \}
$$

for all $x \in |D_0|$.)

**Lean 4**

- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/Basic.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/Basic.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/BasicInst8.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/BasicInst8.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/continuous_monotone.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/continuous_monotone.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/continuous_of_monotone_iSupDirected.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/continuous_of_monotone_iSupDirected.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/continuous_toElementMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/continuous_toElementMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/eq_iSupDirected_principal.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/eq_iSupDirected_principal.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/mem_iff_principal_of_continuous.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/mem_iff_principal_of_continuous.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/ofContinuous.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/ofContinuous.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/principalFamily_directed.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/principalFamily_directed.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/toElementMap_ofContinuous.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise213/toElementMap_ofContinuous.lean)
