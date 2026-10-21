# Exercise 3.16

**EXERCISE 3.16.** Let $\mathcal{D}$ be a given neighbourhood system over $\Delta \subseteq \Sigma^*$. Define

$$
\Delta^\infty = \bigcup_{n=0}^\infty 1^n 0 \Delta,
$$

so that $\Delta^\infty$ is split into infinitely many disjoint copies of $\Delta$. Let $\mathcal{D}^\infty$ be the least family of subsets of $\Sigma^*$ where

1. $\Delta^\infty \in \mathcal{D}^\infty$, and
2. whenever $X \in \mathcal{D}$ and $Y \in \mathcal{D}^\infty$, then $0X \cup 1Y \in \mathcal{D}^\infty$.

Show that $\mathcal{D}^\infty$ is a neighbourhood system over $\Delta^\infty$. Prove the isomorphism

$$
\mathcal{D}^\infty \cong \mathcal{D} \times \mathcal{D}^\infty.
$$

Show, moreover, that the elements of $|\mathcal{D}^\infty|$ are in a one-one correspondence with arbitrary infinite sequences $\langle x_n \rangle_{n=0}^\infty$ of elements $x_n \in |\mathcal{D}|$ by using combinations of neighbourhoods

$$
0X_0 \cup 10X_1 \cup \cdots \cup 1^n 0X_n \cup \cdots,
$$

where from some point on all the $X_m$ are equal to $\Delta$.

**Lean 4**

- [NeighbourhoodSystems/DomainConstructs/Exercise316.lean](../Exercise316.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/component.lean](component.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/component_ofSeq.lean](component_ofSeq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/eq_of_fiber_eq.lean](eq_of_fiber_eq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber.lean](fiber.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_inter.lean](fiber_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_iterSys_master.lean](fiber_iterSys_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_mono.lean](fiber_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_single_ne.lean](fiber_single_ne.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/fiber_single_self.lean](fiber_single_self.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/interUpTo_subset_master.lean](interUpTo_subset_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iterProdIso.lean](iterProdIso.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iterSeqEquiv.lean](iterSeqEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iterSys.lean](iterSys.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iterSys_master.lean](iterSys_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/iter_isomorphic.lean](iter_isomorphic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/le_of_component_le.lean](le_of_component_le.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/mem_component.lean](mem_component.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/mem_fiber.lean](mem_fiber.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/mem_iterSys.lean](mem_iterSys.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/mem_ofSeq.lean](mem_ofSeq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/natShiftEquiv.lean](natShiftEquiv.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/ofSeq.lean](ofSeq.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/ofSeq_component.lean](ofSeq_component.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/ofSeq_mono.lean](ofSeq_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/projN.lean](projN.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/reconstruct_subset.lean](reconstruct_subset.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single.lean](single.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single_inter.lean](single_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single_master.lean](single_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single_mem.lean](single_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/single_mono.lean](single_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise316/subset_single.lean](subset_single.lean)
