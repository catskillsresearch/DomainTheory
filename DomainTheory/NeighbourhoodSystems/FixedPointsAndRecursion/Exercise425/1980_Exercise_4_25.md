# Exercise 4.25

**EXERCISE 4.25.** Perhaps the domains $\mathbf{N}$ and $C$ are not exactly analogous? $C$ was based on $\{0,1\}$ as the underlying set of tokens. Construct a system $C_1$ based on $\{1\}^*$ (= finite strings of 1's) with neighbourhoods:

$$
C_1 = \{\, \{1^m \mid m > n\} \mid n \in \mathbf{N} \,\} \cup \{\, \{1^n\} \mid n \in \mathbf{N} \,\}.
$$

What structure should be put on $C_1$ strictly analogous to that on $C (= C_2)$? What kinds of approximable maps relate $\mathbf{N}$, $C_1$, and $C_2$? Draw some pictures.

**Lean 4**

- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/Basic.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/Basic.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1_master.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1_master.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1_mem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/C1_mem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap_oneBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap_oneBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap_oneElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/consMap_oneElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/infElt.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/infElt.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/infElt_eq.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/infElt_eq.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_shift.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_shift.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_tail.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_tail.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_univ.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/memC1_univ.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/mem_tail.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/mem_tail.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/nestedOrDisjoint.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/oneBot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/oneBot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/oneElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/oneElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1_bot.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1_bot.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1_natElem.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/relateNToC1_natElem.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_mono.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_mono.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_singleton.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_singleton.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_tail.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/shift_tail.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/singleton_tail_nd.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/singleton_tail_nd.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/tail.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/tail.lean)
- [NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/tail_zero.lean](DomainTheory/NeighbourhoodSystems/FixedPointsAndRecursion/Exercise425/tail_zero.lean)
