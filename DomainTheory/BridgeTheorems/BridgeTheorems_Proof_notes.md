# Proof notes

### 3.1 Continuous lattices → neighbourhood systems

**Claim.** For a continuous lattice `D`, the sets `↟a = {z | a ≪ z}` form a
`NeighborhoodSystem` on token type `D`, and under `ContinuousLattice` one has an order
isomorphism `D ≃o RoundFilter`.

**Construction.** `wayBelowUp a` is upward closed; `↟⊥ = univ`;
`↟a ∩ ↟b = ↟(a ⊔ b)` (interpolation / directedness of way-below). Principal filters
`toFilter x = {↟a | a ≪ x}` are round: membership of `↟a` yields, by interpolation in a
continuous lattice, some `b` with `a ≪ b ≪ x`, hence `↟b ∈ toFilter x`.

**Why raw `|𝒟|` fails.** The larger filter `{↟a | a ≤ x}` still has `ofFilter = x`
(supremum of codes), but is not equal to `toFilter x` whenever there are elements
way-below strictly below `x`. Roundness (`↟a ∈ f ⇒ ∃ b, a ≪ b ∧ ↟b ∈ f`) cuts exactly
to the image of `toFilter`.

**Axioms.** `domainOrderIso : D ≃o RoundFilter` audits to `{propext, Quot.sound}`.

### 3.2 Neighbourhood systems → information systems

**Claim.** A neighbourhood system equipped with a decidable exhaustive coding
`NbhdBasis ι α` of its neighbourhood family `𝒟` induces an `InfoSys` on tokens `ι`
with `|𝒟| ≃o` the InfoSys domain.

**Construction.** Tokens are neighbourhood indices. Consistency of a finite `u ⊆ ι` is
membership of `⋂_{i∈u} nbhd i` in `𝒟` (empty intersection = master set `Δ`). Entailment
`u ⊢ j` means the intersection is a neighbourhood contained in `nbhd j`. Filters of the
neighbourhood system correspond to InfoSys elements via the coding.

**Constructivity.** `DecidableEq ι` is required so `InfoSys` can use the choice-free
`Finset` prelude from `scott1982`. The proof of `ent_con` avoids classical `by_cases` /
`em`. The maps extract no witnesses; the kernel audit still reports inherited
`Classical.choice` from the Mathlib 4.33 `Finset` instance frontier (§4).

### 3.3 Information systems → neighbourhood systems

**Claim.** For an information system `A`, the basic opens `[u] = {x ∈ |A| | ↑u ⊆ x}`
(`u ∈ Con`) form a `NeighborhoodSystem` on `|A|`, and filters recover elements:
`|A| ≃o` the filter domain.

**Proof note.** Scott’s Factoid 4.6 supplies the basic-open vocabulary. The Lean proof
initially pulled `Classical.choice` through `simp` on `basicOpen_empty` / finset unions;
those simps were removed so the construction extracts no witnesses. The kernel audit
still reports inherited `Classical.choice` through `InfoSys`/`Finset` (§4). Together
with §3.2 this is the **1980 ↔ 1982** equivalence under coding.

### 3.4 Information systems → ideal completion

**Claim.** `|A| ≃o Ideal (FiniteElement A)`, where finite elements are closures `ū` of
consistent finsets (`Factoid 3.5`).

**Construction.** `toIdeal x` is the ideal of finite approximants of `x`; `ofIdeal`
takes directed suprema of finite elements (1982 Factoids 4.4–4.5:
`directedSup`, `eq_directedSup_finiteApproximants`, `compact_closure`). The maps
extract no witnesses; the kernel audit inherits `Classical.choice` through
`InfoSys`/`Finset` (§4).

### 3.5 Algebraic complete lattices → continuous lattices

**Claim.** If every element of a complete lattice is the directed supremum of compact
elements below it (`AlgebraicLattice`), then `ContinuousLattice` holds.

**Proof note.** Order-theoretic compactness implies `Set.Ici k` is Scott-open, hence
`k ≪ y` whenever `k ≤ y`. Algebraicity then yields `y = ⊔{k compact | k ≤ y} ⊆ ⊔{x | x ≪ y}`.
This is the **classical frontier**: Scott’s `≪` is defined topologically in `scott1972`,
so the footprint inherits that classicality even though the order argument is elementary.

### 3.6 Three-presentation equivalence (`presentation_domains_equiv`)

**Claim.** Under `ContinuousLattice D` and `DecidableEq D`,
```
D ≃o RoundFilter ≃o RoundInfoSysElement
```
where `RoundInfoSysElement` is the subtype of elements of the InfoSys coded by
`wayBelowNbhdBasis` (tokens = elements of `D`, neighbourhoods = `↟a`) that correspond
to round filters. An extended form routes through the ideal-completion subtype.

**Glue.** `wayBelowNbhdBasis` packages the `↟`-system as an `NbhdBasis`;
`roundFilter_infoSys_iso` transports roundness along `NbhdBasis.domainOrderIso`;
`presentation_domains_equiv` is the composite with `continuousLattice_roundFilter_iso`.

**What is not claimed.** Raw `|𝒟|` and the full InfoSys domain `|A|` remain properly
larger than `D`. The equivalence is on the **round** corner that matches continuous
lattice points.

**Axioms.** Under Mathlib 4.33 the kernel audit includes
`{propext, Classical.choice, Quot.sound}` through the inherited InfoSys/`Finset`
instance frontier described in §4; the round-filter construction itself performs no
choice-based witness extraction.

### 3.7 Constructions (`infoSys_constructions_equiv`)

#### Products

`|A| × |B| ≃o |A × B|` via 1982 `pairElements` / `fstMap` / `sndMap` (Prop 6.2).
The maps use explicit projections and assembly, with no witness selection.

#### Separated sums

`WithBot (|A| ⊕ |B|) ≃o |A + B|` via `inl` / `inr` classify-and-assemble (Prop 6.4).
Trichotomy on token polarity uses classical case-split (`Classical.choice` in the
footprint).

#### Function spaces

`ApproximableMap A B ≃o |A → B|` packages Theorem 7.2
(`approxMap_toElement` / `element_toApproxMap`) with pointwise `Le` as `PartialOrder`.
No additional choice is used beyond the inherited InfoSys/`Finset` instance frontier.

#### Factoid 4.6 bridge

`ApproximableMap A B ≃o ScottContinuous A B` via `toScottContinuous` /
`ofScottContinuous`, using Prop 5.3(v) (`rel_iff_closure_le`) and
`closure_le_element` for the round-trip on relations. The relation-level proof performs
no witness extraction; its kernel audit inherits the InfoSys/`Finset` frontier in §4.

#### ScottMap conjugation

A 1972 `ScottMap D E` conjugates along any pair of order isomorphisms
`ιD : D ≃o D'`, `ιE : E ≃o E'` to a pointwise-ordered map `D' → E'`. Specializing to
`continuousLattice_roundFilter_iso` / `presentation_domains_equiv` yields
`scottMap_roundFilter_iso` and `scottMap_roundInfoSys_iso`. The conjugation itself is
order-theoretic; the footprint includes `Classical.choice` because `ScottMap` is defined
via Scott continuity in `scott1972`.

**Out of scope (documented).** Identifying `ApproximableMap` on the coded `↟`-InfoSys
with `ScottMap D E` (needs roundness preservation of approximable maps), and relating
`wayBelow(D × E)` to the InfoSys product of factors (cylinder basis).

**Lean 4**

- [BridgeTheorems/ConjScottMap.lean](ConjScottMap.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp.lean](ContinuousLatticeToNeighborhood/wayBelowUp.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp_anti.lean](ContinuousLatticeToNeighborhood/wayBelowUp_anti.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp_bot.lean](ContinuousLatticeToNeighborhood/wayBelowUp_bot.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp_inter.lean](ContinuousLatticeToNeighborhood/wayBelowUp_inter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toNeighborhoodSystem.lean](ContinuousLatticeToNeighborhood/toNeighborhoodSystem.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/Filter.lean](ContinuousLatticeToNeighborhood/Filter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/Round.lean](ContinuousLatticeToNeighborhood/Round.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/RoundFilter.lean](ContinuousLatticeToNeighborhood/RoundFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/codes.lean](ContinuousLatticeToNeighborhood/codes.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/bot_mem_codes.lean](ContinuousLatticeToNeighborhood/bot_mem_codes.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/codes_directed.lean](ContinuousLatticeToNeighborhood/codes_directed.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/codes_nonempty.lean](ContinuousLatticeToNeighborhood/codes_nonempty.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/ofFilter.lean](ContinuousLatticeToNeighborhood/ofFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/mem_wayBelowUp_ofFilter_of_round.lean](ContinuousLatticeToNeighborhood/mem_wayBelowUp_ofFilter_of_round.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter.lean](ContinuousLatticeToNeighborhood/toFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/mem_wayBelowUp_toFilter.lean](ContinuousLatticeToNeighborhood/mem_wayBelowUp_toFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/ofFilter_toFilter.lean](ContinuousLatticeToNeighborhood/ofFilter_toFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter_isRound.lean](ContinuousLatticeToNeighborhood/toFilter_isRound.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter_mono.lean](ContinuousLatticeToNeighborhood/toFilter_mono.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/domainEmbedding.lean](ContinuousLatticeToNeighborhood/domainEmbedding.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter_ofFilter.lean](ContinuousLatticeToNeighborhood/toFilter_ofFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/domainOrderIso.lean](ContinuousLatticeToNeighborhood/domainOrderIso.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/Basic.lean](ContinuousLatticeToNeighborhood/Basic.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/codes_lower.lean](ContinuousLatticeToNeighborhood/codes_lower.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/mem_codes_iff.lean](ContinuousLatticeToNeighborhood/mem_codes_iff.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood.lean](ContinuousLatticeToNeighborhood.lean)
- [BridgeTheorems/InfoSysConstructions/assembleSum.lean](InfoSysConstructions/assembleSum.lean)
- [BridgeTheorems/InfoSysConstructions/assembleSum_mono.lean](InfoSysConstructions/assembleSum_mono.lean)
- [BridgeTheorems/InfoSysConstructions/instPartialOrderApproximableMap.lean](InfoSysConstructions/instPartialOrderApproximableMap.lean)
- [BridgeTheorems/InfoSysConstructions/approxMap_toElement_le_iff.lean](InfoSysConstructions/approxMap_toElement_le_iff.lean)
- [BridgeTheorems/InfoSysConstructions/functionSpaceDomainIso.lean](InfoSysConstructions/functionSpaceDomainIso.lean)
- [BridgeTheorems/InfoSysConstructions/lftFinset_singleton_right.lean](InfoSysConstructions/lftFinset_singleton_right.lean)
- [BridgeTheorems/InfoSysConstructions/not_left_mem_sum_botElement.lean](InfoSysConstructions/not_left_mem_sum_botElement.lean)
- [BridgeTheorems/InfoSysConstructions/not_right_mem_sum_botElement.lean](InfoSysConstructions/not_right_mem_sum_botElement.lean)
- [BridgeTheorems/InfoSysConstructions/pairElements_mono.lean](InfoSysConstructions/pairElements_mono.lean)
- [BridgeTheorems/InfoSysConstructions/pairElements_unpair.lean](InfoSysConstructions/pairElements_unpair.lean)
- [BridgeTheorems/InfoSysConstructions/rhtFinset_singleton_left.lean](InfoSysConstructions/rhtFinset_singleton_left.lean)
- [BridgeTheorems/InfoSysConstructions/left_bot_mem_inlMap_toElement.lean](InfoSysConstructions/left_bot_mem_inlMap_toElement.lean)
- [BridgeTheorems/InfoSysConstructions/right_bot_mem_inrMap_toElement.lean](InfoSysConstructions/right_bot_mem_inrMap_toElement.lean)
- [BridgeTheorems/InfoSysConstructions/sumElementLft_inlMap_toElement.lean](InfoSysConstructions/sumElementLft_inlMap_toElement.lean)
- [BridgeTheorems/InfoSysConstructions/inlMap_toElement_injective.lean](InfoSysConstructions/inlMap_toElement_injective.lean)
- [BridgeTheorems/InfoSysConstructions/inlMap_toElement_le_iff.lean](InfoSysConstructions/inlMap_toElement_le_iff.lean)
- [BridgeTheorems/InfoSysConstructions/sumElementRht_inrMap_toElement.lean](InfoSysConstructions/sumElementRht_inrMap_toElement.lean)
- [BridgeTheorems/InfoSysConstructions/inrMap_toElement_injective.lean](InfoSysConstructions/inrMap_toElement_injective.lean)
- [BridgeTheorems/InfoSysConstructions/assembleSum_injective.lean](InfoSysConstructions/assembleSum_injective.lean)
- [BridgeTheorems/InfoSysConstructions/inrMap_toElement_le_iff.lean](InfoSysConstructions/inrMap_toElement_le_iff.lean)
- [BridgeTheorems/InfoSysConstructions/sum_element_trichotomy.lean](InfoSysConstructions/sum_element_trichotomy.lean)
- [BridgeTheorems/InfoSysConstructions/exists_assembleSum_eq.lean](InfoSysConstructions/exists_assembleSum_eq.lean)
- [BridgeTheorems/InfoSysConstructions/classifySum.lean](InfoSysConstructions/classifySum.lean)
- [BridgeTheorems/InfoSysConstructions/assembleSum_classifySum.lean](InfoSysConstructions/assembleSum_classifySum.lean)
- [BridgeTheorems/InfoSysConstructions/classifySum_assembleSum.lean](InfoSysConstructions/classifySum_assembleSum.lean)
- [BridgeTheorems/InfoSysConstructions/sumDomainIso.lean](InfoSysConstructions/sumDomainIso.lean)
- [BridgeTheorems/InfoSysConstructions/unpair.lean](InfoSysConstructions/unpair.lean)
- [BridgeTheorems/InfoSysConstructions/unpair_pairElements.lean](InfoSysConstructions/unpair_pairElements.lean)
- [BridgeTheorems/InfoSysConstructions/productDomainIso.lean](InfoSysConstructions/productDomainIso.lean)
- [BridgeTheorems/InfoSysConstructions/Basic.lean](InfoSysConstructions/Basic.lean)
- [BridgeTheorems/InfoSysConstructions/sumElementLft_eq.lean](InfoSysConstructions/sumElementLft_eq.lean)
- [BridgeTheorems/InfoSysConstructions/sumElementRht_eq.lean](InfoSysConstructions/sumElementRht_eq.lean)
- [BridgeTheorems/InfoSysConstructions/unpair_mono.lean](InfoSysConstructions/unpair_mono.lean)
- [BridgeTheorems/InfoSysConstructions.lean](InfoSysConstructions.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/FiniteElement.lean](InfoSysToIdealCompletion/FiniteElement.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/finiteApproximants.lean](InfoSysToIdealCompletion/finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/directed_finiteApproximants.lean](InfoSysToIdealCompletion/directed_finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/idealCarrier.lean](InfoSysToIdealCompletion/idealCarrier.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/directed_idealCarrier.lean](InfoSysToIdealCompletion/directed_idealCarrier.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/isFinite_bot.lean](InfoSysToIdealCompletion/isFinite_bot.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/botFinite.lean](InfoSysToIdealCompletion/botFinite.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/le_of_mem_finiteApproximants.lean](InfoSysToIdealCompletion/le_of_mem_finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/mem_finiteApproximants_of_le.lean](InfoSysToIdealCompletion/mem_finiteApproximants_of_le.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/isLowerSet_finiteApproximants.lean](InfoSysToIdealCompletion/isLowerSet_finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/nonempty_finiteApproximants.lean](InfoSysToIdealCompletion/nonempty_finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/nonempty_idealCarrier.lean](InfoSysToIdealCompletion/nonempty_idealCarrier.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/ofIdeal.lean](InfoSysToIdealCompletion/ofIdeal.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/le_ofIdeal_of_mem.lean](InfoSysToIdealCompletion/le_ofIdeal_of_mem.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/toIdeal.lean](InfoSysToIdealCompletion/toIdeal.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/ofIdeal_toIdeal.lean](InfoSysToIdealCompletion/ofIdeal_toIdeal.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/toIdeal_mono.lean](InfoSysToIdealCompletion/toIdeal_mono.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/toIdeal_ofIdeal.lean](InfoSysToIdealCompletion/toIdeal_ofIdeal.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/domainOrderIso.lean](InfoSysToIdealCompletion/domainOrderIso.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/Basic.lean](InfoSysToIdealCompletion/Basic.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/mem_finiteApproximants_iff.lean](InfoSysToIdealCompletion/mem_finiteApproximants_iff.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/mem_toIdeal_iff.lean](InfoSysToIdealCompletion/mem_toIdeal_iff.lean)
- [BridgeTheorems/InfoSysToIdealCompletion.lean](InfoSysToIdealCompletion.lean)
- [BridgeTheorems/IsCompactElement.lean](IsCompactElement.lean)
- [BridgeTheorems/AlgebraicLattice.lean](AlgebraicLattice.lean)
- [BridgeTheorems/IdealCompletionToContinuousLattice.lean](IdealCompletionToContinuousLattice.lean)
- [BridgeTheorems/NbhdBasis.lean](NbhdBasis.lean)
- [BridgeTheorems/basicOpen_empty.lean](basicOpen_empty.lean)
- [BridgeTheorems/ent_of_basicOpen_subset.lean](ent_of_basicOpen_subset.lean)
- [BridgeTheorems/con_of_basicOpen_subset.lean](con_of_basicOpen_subset.lean)
- [BridgeTheorems/funion_singleton_eq_insert.lean](funion_singleton_eq_insert.lean)
- [BridgeTheorems/basicOpen_singleton_inter.lean](basicOpen_singleton_inter.lean)
- [BridgeTheorems/interOf.lean](interOf.lean)
- [BridgeTheorems/interOf_empty.lean](interOf_empty.lean)
- [BridgeTheorems/interOf_insert.lean](interOf_insert.lean)
- [BridgeTheorems/filter_mem_interOf.lean](filter_mem_interOf.lean)
- [BridgeTheorems/interOf_mem_of_lower_bound.lean](interOf_mem_of_lower_bound.lean)
- [BridgeTheorems/mem_basicOpen_singleton.lean](mem_basicOpen_singleton.lean)
- [BridgeTheorems/mem_interOf.lean](mem_interOf.lean)
- [BridgeTheorems/interOf_anti.lean](interOf_anti.lean)
- [BridgeTheorems/interOf_subset_master.lean](interOf_subset_master.lean)
- [BridgeTheorems/interOf_subset_nbhd.lean](interOf_subset_nbhd.lean)
- [BridgeTheorems/nbhd_subset_master.lean](nbhd_subset_master.lean)
- [BridgeTheorems/interOf_singleton.lean](interOf_singleton.lean)
- [BridgeTheorems/scottContinuous_ext.lean](scottContinuous_ext.lean)
- [BridgeTheorems/ScottMapBridgeInst9.lean](ScottMapBridgeInst9.lean)
- [BridgeTheorems/conjScottMapFun.lean](conjScottMapFun.lean)
- [BridgeTheorems/ScottMapBridgeInst19.lean](ScottMapBridgeInst19.lean)
- [BridgeTheorems/conjScottMapFun_le_iff.lean](conjScottMapFun_le_iff.lean)
- [BridgeTheorems/ext.lean](ext.lean)
- [BridgeTheorems/ScottMapBridgeInst21.lean](ScottMapBridgeInst21.lean)
- [BridgeTheorems/ofScottContinuous_toScottContinuous.lean](ofScottContinuous_toScottContinuous.lean)
- [BridgeTheorems/orderIso.lean](orderIso.lean)
- [BridgeTheorems/toInfoSys.lean](toInfoSys.lean)
- [BridgeTheorems/ofElement.lean](ofElement.lean)
- [BridgeTheorems/ofElement_mem.lean](ofElement_mem.lean)
- [BridgeTheorems/toElement.lean](toElement.lean)
- [BridgeTheorems/ofElement_toElement.lean](ofElement_toElement.lean)
- [BridgeTheorems/toElement_carrier.lean](toElement_carrier.lean)
- [BridgeTheorems/toElement_ofElement.lean](toElement_ofElement.lean)
- [BridgeTheorems/NeighborhoodToInfoSys/domainOrderIso.lean](NeighborhoodToInfoSys/domainOrderIso.lean)
- [BridgeTheorems/NeighborhoodToInfoSys.lean](NeighborhoodToInfoSys.lean)
- [BridgeTheorems/toNeighborhoodSystem.lean](toNeighborhoodSystem.lean)
- [BridgeTheorems/mem_basicOpen_of_singletons.lean](mem_basicOpen_of_singletons.lean)
- [BridgeTheorems/ofFilter.lean](ofFilter.lean)
- [BridgeTheorems/mem_basicOpen_iff.lean](mem_basicOpen_iff.lean)
- [BridgeTheorems/toFilter.lean](toFilter.lean)
- [BridgeTheorems/ofFilter_toFilter.lean](ofFilter_toFilter.lean)
- [BridgeTheorems/toFilter_ofFilter.lean](toFilter_ofFilter.lean)
- [BridgeTheorems/InfoSysToNeighborhood/domainOrderIso.lean](InfoSysToNeighborhood/domainOrderIso.lean)
- [BridgeTheorems/InfoSysToNeighborhood.lean](InfoSysToNeighborhood.lean)
- [BridgeTheorems/PresentationDomains/continuousLattice_roundFilter_iso.lean](PresentationDomains/continuousLattice_roundFilter_iso.lean)
- [BridgeTheorems/PresentationDomains/nbhdBasis_ideal_iso.lean](PresentationDomains/nbhdBasis_ideal_iso.lean)
- [BridgeTheorems/PresentationDomains/neighborhood_ideal_iso.lean](PresentationDomains/neighborhood_ideal_iso.lean)
- [BridgeTheorems/PresentationDomains/wayBelowNbhdBasis.lean](PresentationDomains/wayBelowNbhdBasis.lean)
- [BridgeTheorems/PresentationDomains/IsRoundInfoSysElement.lean](PresentationDomains/IsRoundInfoSysElement.lean)
- [BridgeTheorems/PresentationDomains/RoundInfoSysElement.lean](PresentationDomains/RoundInfoSysElement.lean)
- [BridgeTheorems/PresentationDomains/roundFilter_infoSys_iso.lean](PresentationDomains/roundFilter_infoSys_iso.lean)
- [BridgeTheorems/PresentationDomains/continuousLattice_roundInfoSys_iso.lean](PresentationDomains/continuousLattice_roundInfoSys_iso.lean)
- [BridgeTheorems/PresentationDomains/presentation_domains_equiv.lean](PresentationDomains/presentation_domains_equiv.lean)
- [BridgeTheorems/PresentationDomains/roundInfoSys_ideal_iso.lean](PresentationDomains/roundInfoSys_ideal_iso.lean)
- [BridgeTheorems/PresentationDomains/presentation_domains_equiv_ideal.lean](PresentationDomains/presentation_domains_equiv_ideal.lean)
- [BridgeTheorems/PresentationDomains/Basic.lean](PresentationDomains/Basic.lean)
- [BridgeTheorems/PresentationDomains/wayBelowNbhdBasis_system.lean](PresentationDomains/wayBelowNbhdBasis_system.lean)
- [BridgeTheorems/PresentationDomains.lean](PresentationDomains.lean)
- [BridgeTheorems/toScottContinuous_ofScottContinuous.lean](toScottContinuous_ofScottContinuous.lean)
- [BridgeTheorems/approximableMap_scottContinuous_equiv.lean](approximableMap_scottContinuous_equiv.lean)
- [BridgeTheorems/ScottMapBridge.lean](ScottMapBridge.lean)
- [BridgeTheorems/Equivalence.lean](Equivalence.lean)
