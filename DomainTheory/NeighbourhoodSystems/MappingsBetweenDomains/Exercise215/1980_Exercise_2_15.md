# Exercise 2.15

**EXERCISE 2.15.** (For topologists.) Consider the one-token system with

$$\mathcal{O} = \{ \{0\}, \emptyset \}.$$

We can regard $|\mathcal{O}|$ as having just two finite elements $\bot$ (bottom) and $\top$ (top), where $\bot \sqsubseteq \top$. For any system $D$, show that the open subsets $U$ of $|D|$ are in a one-one correspondence with the approximable mappings $f : D \to \mathcal{O}$, where the correspondence is given by the equation

$$U = \{ x \in |D| \mid f(x) = \top \}.$$

What are the open subsets of $|\mathcal{O}|$? of $|\mathbb{T}|$? of $|\mathbb{B}|$?

**Lean 4**

- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/Basic.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/Basic.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_ext.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_ext.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_inter_mem.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_inter_mem.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_master.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_master.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_mem.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_mem.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_mem_empty.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_mem_empty.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_mem_univ.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/O_mem_univ.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/basicOpen_empty_eq_singleton_top.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/basicOpen_empty_eq_singleton_top.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/botElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/botElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/botElt_le_topElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/botElt_le_topElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/botElt_ne_topElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/botElt_ne_topElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/element_eq_bot_or_top.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/element_eq_bot_or_top.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/isOpen_mapToOpen.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/isOpen_mapToOpen.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/mapToOpen.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/mapToOpen.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/memO.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/memO.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/mem_botElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/mem_botElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/mem_empty_iff_eq_top.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/mem_empty_iff_eq_top.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/mem_mapToOpen_openToMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/mem_mapToOpen_openToMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/nestedOrDisjoint_O.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/nestedOrDisjoint_O.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/not_isOpen_singleton_botElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/not_isOpen_singleton_botElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/openSet_equiv_map.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/openSet_equiv_map.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/openToMap.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/openToMap.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/openToMap_mapToOpen.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/openToMap_mapToOpen.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/subMaster_O.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/subMaster_O.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/toElementMap_openToMap_principal_mem_empty.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/toElementMap_openToMap_principal_mem_empty.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/topElt.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/topElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/univ_ne_empty.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise215/univ_ne_empty.lean)
