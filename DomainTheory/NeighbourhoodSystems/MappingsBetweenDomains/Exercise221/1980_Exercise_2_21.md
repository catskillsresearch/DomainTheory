# Exercise 2.21

$$x + 1 = \{n + 1 \mid n \in x\}, \text{ and}$$
$$x - 1 = \{n \mid n + 1 \in x\}.$$

**EXERCISE 2.21.** The system $\mathcal{B}$ of 2.3 has as its total elements only the infinite sequences. Modify the construction of $\mathcal{B}$ to another neighbourhood system $\mathcal{C}$ which has *both* the finite and infinite sequences as total elements. (Hint: $\mathcal{B} \subseteq \mathcal{C}$.) Show that there is an approximable map $xy$ on elements naturally extending ordinary juxtaposition of sequences. (Hint: Write $01001$ for a *total* finite sequence and $01001\perp$ for the corresponding finite partial element. Remember to distinguish between $\Lambda$ (the total empty sequence) and $\perp$ (the undefined sequence). The definition should work out so that if $x$ is an infinite sequence (hence, total), then $xy = x$ for all $y$. What will $xy$ equal if $x$ is not total? In other words, the construction possesses a rather strong left-to-right bias.)

**Lean 4**

- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/bot_lt_Lambda.lean](bot_lt_Lambda.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/cone_not_subset_singleton.lean](cone_not_subset_singleton.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/cone_ne_singleton.lean](cone_ne_singleton.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/cone_singleton_nd.lean](cone_singleton_nd.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/isTotal_singletonElt.lean](isTotal_singletonElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/juxtapose_cone.lean](juxtapose_cone.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/juxtapose_singleton_mem.lean](juxtapose_singleton_mem.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221.lean](../Exercise221.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/memB_imp_memC.lean](memB_imp_memC.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/memC.lean](memC.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/memC_nonempty.lean](memC_nonempty.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/singleton_cone_nd.lean](singleton_cone_nd.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/singleton_singleton_nd.lean](singleton_singleton_nd.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/nestedOrDisjoint_C.lean](nestedOrDisjoint_C.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/C.lean](C.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/C_mem.lean](C_mem.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/C_master.lean](C_master.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/memC_cone.lean](memC_cone.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/memC_singleton.lean](memC_singleton.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/prepend_mono.lean](prepend_mono.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/prepend_singleton.lean](prepend_singleton.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/memC_prepend.lean](memC_prepend.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/prepend_subset_cone.lean](prepend_subset_cone.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/singletonElt.lean](singletonElt.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/Lambda.lean](Lambda.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/subset_singleton_eq.lean](subset_singleton_eq.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/juxtapose.lean](juxtapose.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise221/Basic.lean](Basic.lean)
