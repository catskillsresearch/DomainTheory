# Exercise 3.18

**EXERCISE 3.18.** Let $\mathcal{D}_0$ and $\mathcal{D}_1$ be neighbourhood systems over $\Delta_0$ and $\Delta_1$, where we again assume that these are subsets of $\Sigma^*$. We assume that in addition *no neighbourhood is empty*. Why is this possible without loss of generality?

Define the *sum system* by:

$$
\mathcal{D}_0 + \mathcal{D}_1 = \{\{\Lambda\} \cup 0\Delta_0 \cup 1\Delta_1\} \cup \{0X \mid X \in \mathcal{D}_0\} \cup \{1Y \mid Y \in \mathcal{D}_1\}.
$$

Prove that this is a neighbourhood system over $\{\Lambda\} \cup 0\Delta_0 \cup 1\Delta_1$. (Throwing in $\{\Lambda\}$ was not all that necessary, but note that $\mathcal{B} = \mathcal{B} + \mathcal{B}$, and this is an equality of sets not just an isomorphism of systems.)

Prove that in general there are mappings

$$
in_i : \mathcal{D}_i \to \mathcal{D}_0 + \mathcal{D}_1 \quad \text{and} \quad out_i : \mathcal{D}_0 + \mathcal{D}_1 \to \mathcal{D}_i,
$$

where $out_i \circ in_i = I_{\mathcal{D}_i}$. Where does the assumption $\emptyset \notin \mathcal{D}_i$ come in? How can these sums be generalized to $n$-terms? (Hint: As for products use sets $1^i 0 \Delta_i$.) Draw some pictures.

**Lean 4**

- [NeighbourhoodSystems/DomainConstructs/Exercise318.lean](../Exercise318.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il.lean](il.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il_injective.lean](il_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il_mem_inj₀.lean](il_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il_mem_inj₁.lean](il_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/il_preimage_inj₀.lean](il_preimage_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inMap₀.lean](inMap₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inMap₁.lean](inMap₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inju2080_injective.lean](inju2080_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inju2081_injective.lean](inju2081_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀.lean](inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_inter.lean](inj₀_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_inter_inj₁.lean](inj₀_inter_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_nonempty.lean](inj₀_nonempty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_subset_inj₀.lean](inj₀_subset_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₀_subset_sumMaster.lean](inj₀_subset_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁.lean](inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_inter.lean](inj₁_inter.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_nonempty.lean](inj₁_nonempty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_subset_inj₁.lean](inj₁_subset_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/inj₁_subset_sumMaster.lean](inj₁_subset_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir.lean](ir.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir_injective.lean](ir_injective.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir_mem_inj₀.lean](ir_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir_mem_inj₁.lean](ir_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/ir_preimage_inj₁.lean](ir_preimage_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart.lean](leftPart.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_inj₀.lean](leftPart_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_inj₁.lean](leftPart_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_mem.lean](leftPart_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_mono.lean](leftPart_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/leftPart_sumMaster.lean](leftPart_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/mem_leftPart.lean](mem_leftPart.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/mem_rightPart.lean](mem_rightPart.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/none_mem_inj₀.lean](none_mem_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/none_mem_inj₁.lean](none_mem_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/none_mem_sumMaster.lean](none_mem_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/outMapu2080_comp_inMapu2080.lean](outMapu2080_comp_inMapu2080.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/outMapu2081_comp_inMapu2081.lean](outMapu2081_comp_inMapu2081.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/outMap₀.lean](outMap₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/outMap₁.lean](outMap₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart.lean](rightPart.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_inj₀.lean](rightPart_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_inj₁.lean](rightPart_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_mem.lean](rightPart_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_mono.lean](rightPart_mono.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/rightPart_sumMaster.lean](rightPart_sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/sum.lean](sum.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/sumMaster.lean](sumMaster.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/sumMaster_inter_inj₀.lean](sumMaster_inter_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise318/sumMaster_inter_inj₁.lean](sumMaster_inter_inj₁.lean)
