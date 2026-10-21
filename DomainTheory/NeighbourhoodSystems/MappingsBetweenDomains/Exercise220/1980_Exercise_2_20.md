# Exercise 2.20

**EXERCISE 2.20.** Discuss again the example of Exercise 1.15 where the domain turns out to be the powerset (set of all subsets) of $\mathbf{N}$. Show how the finite elements can be taken to be the finite subsets of $\mathbf{N}$ and can be identified with the tokens of a suitable neighbourhood system $\mathcal{P}$. (Hint: Define $\uparrow F$ for finite sets $F \subseteq \mathbf{N}$.) Show that both union and intersection ($x \cup y$ and $x \cap y$) are functions on $|\mathcal{P}|$ that are approximable in the sense of Exercise 2.19. (The elements of $|\mathcal{P}|$ are being identified with arbitrary sets $x \subseteq \mathbf{N}$.) Show also that the following transformations are approximable:

**Lean 4**

- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/Basic.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/Basic.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/equivSetNat.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/equivSetNat.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/interMap₂.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/interMap₂.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_compl_of_finite.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_compl_of_finite.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_compl_singleton.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_compl_singleton.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_powerSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_powerSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_predSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_predSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_toSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/mem_toSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/ofSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/ofSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/ofSet_mono.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/ofSet_mono.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/ofSet_toSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/ofSet_toSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/powerSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/powerSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/powerSet_inter_mem.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/powerSet_inter_mem.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/powerSet_master.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/powerSet_master.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/predMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/predMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/predSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/predSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/predSet_mono.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/predSet_mono.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/succMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/succMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/succSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/succSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/succSet_mono.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/succSet_mono.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_interMapu2082.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_interMapu2082.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_ofSet.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_ofSet.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_predMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_predMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_succMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_succMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_unionMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/toSet_unionMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/unionMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise220/unionMap.lean)
