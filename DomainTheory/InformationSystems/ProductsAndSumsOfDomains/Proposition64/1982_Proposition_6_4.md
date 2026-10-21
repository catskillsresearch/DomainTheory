# Proposition 6.4

**PROPOSITION 6.4.** If $\mathbf{A}$ and $\mathbf{B}$ are information systems, then so is $\mathbf{A} + \mathbf{B}$, and we have approximable mappings

$$\mathrm{inl} : \mathbf{A} \to \mathbf{A} + \mathbf{B} \quad \text{and} \quad \mathrm{inr} : \mathbf{B} \to \mathbf{A} + \mathbf{B},$$

such that, for approximable mappings

$$f : \mathbf{A} \to \mathbf{C} \quad \text{and} \quad g : \mathbf{B} \to \mathbf{C},$$

there is one and only one approximable mapping $[f, g] : \mathbf{A} + \mathbf{B} \to \mathbf{C}$, such that

$$[f, g] \circ \mathrm{inl} = f, \quad [f, g] \circ \mathrm{inr} = g, \quad \text{and} \quad [f, g](\perp_{\mathbf{A}+\mathbf{B}}) = \perp_{\mathbf{C}}.$$
*Proof.* The proof that 6.3 defines a system satisfying the basic axioms of 2.1 has to be left to the reader. Next using the notation of 6.1, where $\mathrm{lft}$ and $\mathrm{rht}$ were applied as operations on consistent sets $u \in \mathrm{Con}_{\mathbf{A}+\mathbf{B}}$, we redefine matters to have approximable mappings, where, for $v \in \mathrm{Con}_{\mathbf{A}}$ and $w \in \mathrm{Con}_{\mathbf{B}}$,

$(1)$ $v\ \mathrm{inl}\ u$ iff $\{(X, \Delta) \mid X \in v\} \vdash_{\mathbf{A}+\mathbf{B}} u$;

$(2)$ $w\ \mathrm{inr}\ u$ iff $\{(\Delta, Y) \mid Y \in w\} \vdash_{\mathbf{A}+\mathbf{B}} u$; and

$(3)$ $u\ [f, g]\ s$ iff either $\vdash_{\mathbf{C}}\ s$, or $\mathrm{lft}\, u \neq \emptyset$ and $\mathrm{lft}\, u\ f\ s$, or $\mathrm{rht}\, u \neq \emptyset$ and $\mathrm{rht}\, u\ g\ s$.

Because we defined $\mathbf{A} + \mathbf{B}$ so that consistency and entailment worked on the two halves of the set of data objects just as they worked on $\mathbf{A}$ and $\mathbf{B}$, respectively, it is easy to check that (1)–(3) define approximable mappings, and that the desired properties hold.

The uniqueness of $[f, g]$ comes from the fact that the elements of $\mathbf{A} + \mathbf{B}$, apart from the bottom element of the domain, are just the elements in the ranges of $\mathrm{inl}$ and $\mathrm{inr}$. Since the function $[f, g]$ takes bottom to bottom (in the indicated domains), it will be uniquely determined by what it does on the two halves of the sum. The last equations of the theorem just say that the function is completely determined on these elements. $\blacksquare$

**Lean 4**

- [InformationSystems/ProductsAndSumsOfDomains/Proposition64.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/Basic.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/Basic.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/SumCon_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inlMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inlMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inrMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/comp_copairMap_inrMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_botElement.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_botElement.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_unique.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copairMap_unique.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/copair_union_disj.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/copair_union_disj.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_empty_of_rel_bot_like.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_empty_of_rel_bot_like.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_lft_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_lft_of_sumEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftLft_of_left_only.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftLft_of_left_only.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftRht_of_right_only.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_liftRht_of_right_only.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_rht_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_rht_of_sumEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inl_witness.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inl_witness.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inr_witness.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/entSet_u_of_inr_witness.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/eq_botElement_of_no_injections.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/eq_botElement_of_no_injections.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap_toElement_sumElementLft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inlMap_toElement_sumElementLft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap_toElement_sumElementRht.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/inrMap_toElement_sumElementRht.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/instLeftCommutativeLiftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_eq_empty_or_mem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_eq_empty_or_mem.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lftFinset_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_eq_empty_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_eq_empty_of_sumEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_mem_Con_of_SumCon_rht_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/lft_mem_Con_of_SumCon_rht_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_foldr_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/mem_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/not_mem_right_of_mem_left.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/not_mem_right_of_mem_left.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_eq_empty_or_mem.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_eq_empty_or_mem.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumLeft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumLeft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumRight.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rhtFinset_liftSumRight.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_eq_empty_of_sumEntSet.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_eq_empty_of_sumEntSet.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_mem_Con_of_SumCon_lft_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/rht_mem_Con_of_SumCon_lft_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/subset_botElement_of_projections_empty.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/subset_botElement_of_projections_empty.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementLft.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementLft.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementRht.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumElementRht.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumLftCarrier.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumLftCarrier.lean)
- [InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumRhtCarrier.lean](DomainTheory/InformationSystems/ProductsAndSumsOfDomains/Proposition64/sumRhtCarrier.lean)
