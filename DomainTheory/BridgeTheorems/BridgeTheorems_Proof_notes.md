# Proof notes

### 3.1 Continuous lattices → neighbourhood systems

**Claim.** For a continuous lattice `D`, the sets `↟a = {z | a ≪ z}` form a
`NeighborhoodSystem` on token type `D`, and under `IsContinuousLattice` one has an order
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
elements below it (`IsAlgebraicLattice`), then `IsContinuousLattice` holds.

**Proof note.** Order-theoretic compactness implies `Set.Ici k` is Scott-open, hence
`k ≪ y` whenever `k ≤ y`. Algebraicity then yields `y = ⊔{k compact | k ≤ y} ⊆ ⊔{x | x ≪ y}`.
This is the **classical frontier**: Scott’s `≪` is defined topologically in `scott1972`,
so the footprint inherits that classicality even though the order argument is elementary.

### 3.6 Three-presentation equivalence (`presentation_domains_equiv`)

**Claim.** Under `IsContinuousLattice D` and `DecidableEq D`,
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

- [BridgeTheorems/ConjScottMap.lean](DomainTheory/BridgeTheorems/ConjScottMap.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/Basic.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/Basic.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/Filter.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/Filter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/IsRound.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/IsRound.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/RoundFilter.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/RoundFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/bot_mem_codes.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/bot_mem_codes.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/codes.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/codes.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/codes_directed.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/codes_directed.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/codes_lower.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/codes_lower.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/codes_nonempty.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/codes_nonempty.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/domainEmbedding.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/domainEmbedding.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/domainOrderIso.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/domainOrderIso.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/mem_codes_iff.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/mem_codes_iff.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/mem_wayBelowUp_ofFilter_of_round.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/mem_wayBelowUp_ofFilter_of_round.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/mem_wayBelowUp_toFilter.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/mem_wayBelowUp_toFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/ofFilter.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/ofFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/ofFilter_toFilter.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/ofFilter_toFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter_isRound.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter_isRound.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter_mono.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter_mono.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter_ofFilter.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/toFilter_ofFilter.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/toNeighborhoodSystem.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/toNeighborhoodSystem.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp_anti.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp_anti.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp_bot.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp_bot.lean)
- [BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp_inter.lean](DomainTheory/BridgeTheorems/ContinuousLatticeToNeighborhood/wayBelowUp_inter.lean)
- [BridgeTheorems/Equivalence.lean](DomainTheory/BridgeTheorems/Equivalence.lean)
- [BridgeTheorems/IdealCompletionToContinuousLattice.lean](DomainTheory/BridgeTheorems/IdealCompletionToContinuousLattice.lean)
- [BridgeTheorems/InfoSysConstructions.lean](DomainTheory/BridgeTheorems/InfoSysConstructions.lean)
- [BridgeTheorems/InfoSysConstructions/Basic.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/Basic.lean)
- [BridgeTheorems/InfoSysConstructions/approxMap_toElement_le_iff.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/approxMap_toElement_le_iff.lean)
- [BridgeTheorems/InfoSysConstructions/assembleSum.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/assembleSum.lean)
- [BridgeTheorems/InfoSysConstructions/assembleSum_classifySum.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/assembleSum_classifySum.lean)
- [BridgeTheorems/InfoSysConstructions/assembleSum_injective.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/assembleSum_injective.lean)
- [BridgeTheorems/InfoSysConstructions/assembleSum_mono.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/assembleSum_mono.lean)
- [BridgeTheorems/InfoSysConstructions/classifySum.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/classifySum.lean)
- [BridgeTheorems/InfoSysConstructions/classifySum_assembleSum.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/classifySum_assembleSum.lean)
- [BridgeTheorems/InfoSysConstructions/exists_assembleSum_eq.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/exists_assembleSum_eq.lean)
- [BridgeTheorems/InfoSysConstructions/functionSpaceDomainIso.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/functionSpaceDomainIso.lean)
- [BridgeTheorems/InfoSysConstructions/inlMap_toElement_injective.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/inlMap_toElement_injective.lean)
- [BridgeTheorems/InfoSysConstructions/inlMap_toElement_le_iff.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/inlMap_toElement_le_iff.lean)
- [BridgeTheorems/InfoSysConstructions/inrMap_toElement_injective.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/inrMap_toElement_injective.lean)
- [BridgeTheorems/InfoSysConstructions/inrMap_toElement_le_iff.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/inrMap_toElement_le_iff.lean)
- [BridgeTheorems/InfoSysConstructions/instPartialOrderApproximableMap.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/instPartialOrderApproximableMap.lean)
- [BridgeTheorems/InfoSysConstructions/left_bot_mem_inlMap_toElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/left_bot_mem_inlMap_toElement.lean)
- [BridgeTheorems/InfoSysConstructions/lftFinset_singleton_right.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/lftFinset_singleton_right.lean)
- [BridgeTheorems/InfoSysConstructions/not_left_mem_sum_botElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/not_left_mem_sum_botElement.lean)
- [BridgeTheorems/InfoSysConstructions/not_right_mem_sum_botElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/not_right_mem_sum_botElement.lean)
- [BridgeTheorems/InfoSysConstructions/pairElements_mono.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/pairElements_mono.lean)
- [BridgeTheorems/InfoSysConstructions/pairElements_unpair.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/pairElements_unpair.lean)
- [BridgeTheorems/InfoSysConstructions/productDomainIso.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/productDomainIso.lean)
- [BridgeTheorems/InfoSysConstructions/rhtFinset_singleton_left.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/rhtFinset_singleton_left.lean)
- [BridgeTheorems/InfoSysConstructions/right_bot_mem_inrMap_toElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/right_bot_mem_inrMap_toElement.lean)
- [BridgeTheorems/InfoSysConstructions/sumDomainIso.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumDomainIso.lean)
- [BridgeTheorems/InfoSysConstructions/sumElementLft_eq.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumElementLft_eq.lean)
- [BridgeTheorems/InfoSysConstructions/sumElementLft_inlMap_toElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumElementLft_inlMap_toElement.lean)
- [BridgeTheorems/InfoSysConstructions/sumElementRht_eq.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumElementRht_eq.lean)
- [BridgeTheorems/InfoSysConstructions/sumElementRht_inrMap_toElement.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sumElementRht_inrMap_toElement.lean)
- [BridgeTheorems/InfoSysConstructions/sum_element_trichotomy.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/sum_element_trichotomy.lean)
- [BridgeTheorems/InfoSysConstructions/unpair.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/unpair.lean)
- [BridgeTheorems/InfoSysConstructions/unpair_mono.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/unpair_mono.lean)
- [BridgeTheorems/InfoSysConstructions/unpair_pairElements.lean](DomainTheory/BridgeTheorems/InfoSysConstructions/unpair_pairElements.lean)
- [BridgeTheorems/InfoSysToIdealCompletion.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/Basic.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/Basic.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/FiniteElement.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/FiniteElement.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/botFinite.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/botFinite.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/directed_finiteApproximants.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/directed_finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/directed_idealCarrier.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/directed_idealCarrier.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/domainOrderIso.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/domainOrderIso.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/finiteApproximants.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/idealCarrier.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/idealCarrier.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/isFinite_bot.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/isFinite_bot.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/isLowerSet_finiteApproximants.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/isLowerSet_finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/le_ofIdeal_of_mem.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/le_ofIdeal_of_mem.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/le_of_mem_finiteApproximants.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/le_of_mem_finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/mem_finiteApproximants_iff.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/mem_finiteApproximants_iff.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/mem_finiteApproximants_of_le.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/mem_finiteApproximants_of_le.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/mem_toIdeal_iff.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/mem_toIdeal_iff.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/nonempty_finiteApproximants.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/nonempty_finiteApproximants.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/nonempty_idealCarrier.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/nonempty_idealCarrier.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/ofIdeal.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/ofIdeal.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/ofIdeal_toIdeal.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/ofIdeal_toIdeal.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/toIdeal.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/toIdeal.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/toIdeal_mono.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/toIdeal_mono.lean)
- [BridgeTheorems/InfoSysToIdealCompletion/toIdeal_ofIdeal.lean](DomainTheory/BridgeTheorems/InfoSysToIdealCompletion/toIdeal_ofIdeal.lean)
- [BridgeTheorems/InfoSysToNeighborhood.lean](DomainTheory/BridgeTheorems/InfoSysToNeighborhood.lean)
- [BridgeTheorems/InfoSysToNeighborhood/domainOrderIso.lean](DomainTheory/BridgeTheorems/InfoSysToNeighborhood/domainOrderIso.lean)
- [BridgeTheorems/IsAlgebraicLattice.lean](DomainTheory/BridgeTheorems/IsAlgebraicLattice.lean)
- [BridgeTheorems/IsCompactElement.lean](DomainTheory/BridgeTheorems/IsCompactElement.lean)
- [BridgeTheorems/NbhdBasis.lean](DomainTheory/BridgeTheorems/NbhdBasis.lean)
- [BridgeTheorems/NeighborhoodToInfoSys.lean](DomainTheory/BridgeTheorems/NeighborhoodToInfoSys.lean)
- [BridgeTheorems/NeighborhoodToInfoSys/domainOrderIso.lean](DomainTheory/BridgeTheorems/NeighborhoodToInfoSys/domainOrderIso.lean)
- [BridgeTheorems/PresentationDomains.lean](DomainTheory/BridgeTheorems/PresentationDomains.lean)
- [BridgeTheorems/PresentationDomains/Basic.lean](DomainTheory/BridgeTheorems/PresentationDomains/Basic.lean)
- [BridgeTheorems/PresentationDomains/IsRoundInfoSysElement.lean](DomainTheory/BridgeTheorems/PresentationDomains/IsRoundInfoSysElement.lean)
- [BridgeTheorems/PresentationDomains/RoundInfoSysElement.lean](DomainTheory/BridgeTheorems/PresentationDomains/RoundInfoSysElement.lean)
- [BridgeTheorems/PresentationDomains/continuousLattice_roundFilter_iso.lean](DomainTheory/BridgeTheorems/PresentationDomains/continuousLattice_roundFilter_iso.lean)
- [BridgeTheorems/PresentationDomains/continuousLattice_roundInfoSys_iso.lean](DomainTheory/BridgeTheorems/PresentationDomains/continuousLattice_roundInfoSys_iso.lean)
- [BridgeTheorems/PresentationDomains/nbhdBasis_ideal_iso.lean](DomainTheory/BridgeTheorems/PresentationDomains/nbhdBasis_ideal_iso.lean)
- [BridgeTheorems/PresentationDomains/neighborhood_ideal_iso.lean](DomainTheory/BridgeTheorems/PresentationDomains/neighborhood_ideal_iso.lean)
- [BridgeTheorems/PresentationDomains/presentation_domains_equiv.lean](DomainTheory/BridgeTheorems/PresentationDomains/presentation_domains_equiv.lean)
- [BridgeTheorems/PresentationDomains/presentation_domains_equiv_ideal.lean](DomainTheory/BridgeTheorems/PresentationDomains/presentation_domains_equiv_ideal.lean)
- [BridgeTheorems/PresentationDomains/roundFilter_infoSys_iso.lean](DomainTheory/BridgeTheorems/PresentationDomains/roundFilter_infoSys_iso.lean)
- [BridgeTheorems/PresentationDomains/roundInfoSys_ideal_iso.lean](DomainTheory/BridgeTheorems/PresentationDomains/roundInfoSys_ideal_iso.lean)
- [BridgeTheorems/PresentationDomains/wayBelowNbhdBasis.lean](DomainTheory/BridgeTheorems/PresentationDomains/wayBelowNbhdBasis.lean)
- [BridgeTheorems/PresentationDomains/wayBelowNbhdBasis_system.lean](DomainTheory/BridgeTheorems/PresentationDomains/wayBelowNbhdBasis_system.lean)
- [BridgeTheorems/ScottMapBridge.lean](DomainTheory/BridgeTheorems/ScottMapBridge.lean)
- [BridgeTheorems/ScottMapBridgeInst19.lean](DomainTheory/BridgeTheorems/ScottMapBridgeInst19.lean)
- [BridgeTheorems/ScottMapBridgeInst21.lean](DomainTheory/BridgeTheorems/ScottMapBridgeInst21.lean)
- [BridgeTheorems/ScottMapBridgeInst9.lean](DomainTheory/BridgeTheorems/ScottMapBridgeInst9.lean)
- [BridgeTheorems/WorkedExampleSExpr.lean](DomainTheory/BridgeTheorems/WorkedExampleSExpr.lean)
- [BridgeTheorems/approximableMap_scottContinuous_equiv.lean](DomainTheory/BridgeTheorems/approximableMap_scottContinuous_equiv.lean)
- [BridgeTheorems/basicOpen_empty.lean](DomainTheory/BridgeTheorems/basicOpen_empty.lean)
- [BridgeTheorems/basicOpen_singleton_inter.lean](DomainTheory/BridgeTheorems/basicOpen_singleton_inter.lean)
- [BridgeTheorems/con_of_basicOpen_subset.lean](DomainTheory/BridgeTheorems/con_of_basicOpen_subset.lean)
- [BridgeTheorems/conjScottMapFun.lean](DomainTheory/BridgeTheorems/conjScottMapFun.lean)
- [BridgeTheorems/conjScottMapFun_le_iff.lean](DomainTheory/BridgeTheorems/conjScottMapFun_le_iff.lean)
- [BridgeTheorems/ent_of_basicOpen_subset.lean](DomainTheory/BridgeTheorems/ent_of_basicOpen_subset.lean)
- [BridgeTheorems/ext.lean](DomainTheory/BridgeTheorems/ext.lean)
- [BridgeTheorems/filter_mem_interOf.lean](DomainTheory/BridgeTheorems/filter_mem_interOf.lean)
- [BridgeTheorems/funion_singleton_eq_insert.lean](DomainTheory/BridgeTheorems/funion_singleton_eq_insert.lean)
- [BridgeTheorems/interOf.lean](DomainTheory/BridgeTheorems/interOf.lean)
- [BridgeTheorems/interOf_anti.lean](DomainTheory/BridgeTheorems/interOf_anti.lean)
- [BridgeTheorems/interOf_empty.lean](DomainTheory/BridgeTheorems/interOf_empty.lean)
- [BridgeTheorems/interOf_insert.lean](DomainTheory/BridgeTheorems/interOf_insert.lean)
- [BridgeTheorems/interOf_mem_of_lower_bound.lean](DomainTheory/BridgeTheorems/interOf_mem_of_lower_bound.lean)
- [BridgeTheorems/interOf_singleton.lean](DomainTheory/BridgeTheorems/interOf_singleton.lean)
- [BridgeTheorems/interOf_subset_master.lean](DomainTheory/BridgeTheorems/interOf_subset_master.lean)
- [BridgeTheorems/interOf_subset_nbhd.lean](DomainTheory/BridgeTheorems/interOf_subset_nbhd.lean)
- [BridgeTheorems/mem_basicOpen_iff.lean](DomainTheory/BridgeTheorems/mem_basicOpen_iff.lean)
- [BridgeTheorems/mem_basicOpen_of_singletons.lean](DomainTheory/BridgeTheorems/mem_basicOpen_of_singletons.lean)
- [BridgeTheorems/mem_basicOpen_singleton.lean](DomainTheory/BridgeTheorems/mem_basicOpen_singleton.lean)
- [BridgeTheorems/mem_interOf.lean](DomainTheory/BridgeTheorems/mem_interOf.lean)
- [BridgeTheorems/nbhd_subset_master.lean](DomainTheory/BridgeTheorems/nbhd_subset_master.lean)
- [BridgeTheorems/ofElement.lean](DomainTheory/BridgeTheorems/ofElement.lean)
- [BridgeTheorems/ofElement_mem.lean](DomainTheory/BridgeTheorems/ofElement_mem.lean)
- [BridgeTheorems/ofElement_toElement.lean](DomainTheory/BridgeTheorems/ofElement_toElement.lean)
- [BridgeTheorems/ofFilter.lean](DomainTheory/BridgeTheorems/ofFilter.lean)
- [BridgeTheorems/ofFilter_toFilter.lean](DomainTheory/BridgeTheorems/ofFilter_toFilter.lean)
- [BridgeTheorems/ofScottContinuous_toScottContinuous.lean](DomainTheory/BridgeTheorems/ofScottContinuous_toScottContinuous.lean)
- [BridgeTheorems/orderIso.lean](DomainTheory/BridgeTheorems/orderIso.lean)
- [BridgeTheorems/saturated_of_closed.lean](DomainTheory/BridgeTheorems/saturated_of_closed.lean)
- [BridgeTheorems/scottContinuous_ext.lean](DomainTheory/BridgeTheorems/scottContinuous_ext.lean)
- [BridgeTheorems/toElement.lean](DomainTheory/BridgeTheorems/toElement.lean)
- [BridgeTheorems/toElement_carrier.lean](DomainTheory/BridgeTheorems/toElement_carrier.lean)
- [BridgeTheorems/toElement_ofElement.lean](DomainTheory/BridgeTheorems/toElement_ofElement.lean)
- [BridgeTheorems/toFilter.lean](DomainTheory/BridgeTheorems/toFilter.lean)
- [BridgeTheorems/toFilter_ofFilter.lean](DomainTheory/BridgeTheorems/toFilter_ofFilter.lean)
- [BridgeTheorems/toInfoSys.lean](DomainTheory/BridgeTheorems/toInfoSys.lean)
- [BridgeTheorems/toNeighborhoodSystem.lean](DomainTheory/BridgeTheorems/toNeighborhoodSystem.lean)
- [BridgeTheorems/toScottContinuous_ofScottContinuous.lean](DomainTheory/BridgeTheorems/toScottContinuous_ofScottContinuous.lean)
