# Worked example — S-expressions / trees

Lean packaging:
[`WorkedExampleSExpr.lean`](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/WorkedExampleSExpr.lean),
[`SexDomainEquation.lean`](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/SexDomainEquation.lean).
The Palomar compared family includes `sexNeighborhoodIso`, `sexIdealIso`,
and `sexDomainEquationIso` (Challenge / `comparator.json`). The compared
domain-equation declaration is the order isomorphism
`SexSys.Element ≃o SexRhs.Element` (`|T| ≃o |A + (T × T)|`), not the
generic semantic factor `WithBot (|A| ⊕ (|T| × |T|)) ≃o |A + (T × T)|`.

### 5.1 Overview

The bridges of §§2–3 are abstract. This section fixes **one** concrete domain — Scott’s
S-expression / tree equation `T ≅ A + (T × T)` (**[Sco82]**, Factoid 8.1) over the ℕ
lower-bound atom system (Factoid 2.4) — and asks what that domain looks like in each
paradigm:

| Paradigm | What an element of `T` is |
| --- | --- |
| **1982** | a consistent, deductively closed set of tree tokens |
| **1980** | a filter of basic opens `[u]` on that token domain |
| **1972** | a point of an algebraic continuous lattice (ideal of finite elements) |

We build the domain natively as an information system (§5.2), then **read the same
carrier** as a neighbourhood system (§5.3) and as a continuous lattice (§5.4). Section 5.5
exhibits the order isomorphisms for this instance — so that, on S-expressions,

`T_1982 ≃o T_1980 ≃o Ideal(K(T))`  and  `Ideal(K(T))` is a continuous lattice,

hence transitively `T_1982 ≃o T_1980` and (via the algebraic ⇒ continuous frontier)
the 1972 presentation of the same domain. Order isomorphism is an equivalence relation,
so the three presentations determine one domain up to `≃o`. Section 5.6 records two
extras that live on top of the carriers: the domain equation at the level of domains,
and identity as a morphism in both the approximable-map and Scott-continuous languages.

### 5.2 Information system (1982)

Atoms are propositions `n ≤ x` on `ℕ` (`lowerBoundSystem`). The tree system
`SexSys := treeSystem lowerBoundSystem` has inductive tokens `TreeToken ℕ`
(`bot` / `atom` / `pairL` / `pairR`). Consistency and entailment are Scott’s sum×product
clauses; Factoid 8.1 records that this is literally the information system of the
right-hand side `A + (T × T)`:

- `SexRhs = sumSystem A (productSystem T T)` (`sexRhs_eq_sum_product`);
- token unfolding `treeUnfold` sends `atom n` to the left summand (`sexUnfold_atom`)
  and is a retraction onto the official sum-of-product carrier, with section `treeFold`;
- TreeEnt matches official product `ent_bot` on the two encodings of `(Δ,Δ)`
  (`pairL Δ` and `pairR Δ`), so closed elements are saturated for
  `ker(treeUnfold)`.

Finite elements include singleton atom closures `sexAtom n = ū` for `u = {atom n}`.
Elements of `|T|` are the consistent closed sets of tokens — the 1982 presentation of
the S-expression domain.

### 5.3 Neighbourhood system (1980)

From `|T|` one obtains a neighbourhood system whose basic opens are
`[u] = {x ∈ |T| | ↑u ⊆ x}`. In this paradigm an element of the domain is a
**filter** of such opens (not a raw set of tokens). Nothing new is invented: it is the
image of `SexSys` under `InfoSysToNeighborhood`. The concrete iso of §5.5 below is
exactly “read each token-element as its filter of basic opens.”

### 5.4 Continuous lattice (1972)

Finite elements `K(T)` are the closures of consistent finsets. In the algebraic style
that feeds Scott’s 1972 theory, a domain element is an **ideal** of `K(T)` — the ideal
completion of the compact basis. That poset of ideals is an algebraic complete lattice,
hence a continuous lattice (`AlgebraicLattice ⇒ ContinuousLattice`, §3.5). This is
the 1972 presentation of the same S-expression domain: points ordered by inclusion of
ideals, with way-below recovered from the compact basis.

We do not claim a choice-free `D ≃o RoundFilter` story built from trees alone; the
round `↟`-filter identification of §3.1 applies once one is already in the
continuous-lattice setting.

### 5.5 Equivalence for this instance

Specializing the bridges of §3 to `SexSys` yields order isomorphisms of carriers:

- `sexNeighborhoodIso : |T| ≃o` filters of `[u]`
  (`InfoSysToNeighborhood.domainOrderIso`) — **1982 ≃o 1980**;
- `sexIdealIso : |T| ≃o Ideal (FiniteElement T)`
  (`InfoSysToIdealCompletion.domainOrderIso`) — **1982 ≃o algebraic / 1972 carrier**;
- `sexNeighborhoodIdealIso` (`neighborhood_ideal_iso`) — the constructive triangle
  closing **1980 ≃o Ideal(K(T))** without going back through tokens.

Composing any two edges recovers the third: isomorphism is transitive, so on this
example the three presentations are pairwise equivalent. The 1972 corner uses the
algebraic ⇒ continuous implication already flagged in §3.5 / §4. The neighbourhood
↔ information ↔ ideal triangle inherits `Classical.choice` only through the `Finset`
instance frontier of §4.

### 5.6 Domain equation and morphisms

Beyond identifying the carriers, the same example exercises constructions and maps.

**Domain equation.** Factoid 8.1’s token unfolding `treeUnfold` (section `treeFold`)
lifts to an order isomorphism of the tree domain with the official RHS domain:

`sexDomainEquationIso : SexSys.Element ≃o SexRhs.Element`

(`treeDomainIso`; `|T| ≃o |A + (T × T)|`). The maps are verified unfolding: the
carrier of `sexDomainEquationIso x` is `treeUnfold '' x.carrier`, and the carrier
of the inverse is the preimage `treeUnfold ⁻¹' y.carrier`
(`sexDomainEquationIso_unfold` / `sexDomainEquationIso_fold`). The only
non-injectivity of `treeUnfold` is Scott’s two encodings of the product bottom
(`pairL Δ` and `pairR Δ`); after the `ent_bot` match, closed elements are
saturated for that kernel, so image and preimage invert. The generic semantic
factor `WithBot (|A| ⊕ (|T| × |T|)) ≃o SexRhs.Element` is the uncompared
`sexRhsSemanticIso` (classical only through the 1982 sum trichotomy); it is
**not** the compared fixed-point equation.

**Morphisms.** The identity approximable map `idMap T` (Prop 5.4) transports along
Factoid 4.6 to a Scott-continuous endomap `sexIdScottContinuous` with `toFun = id`
(`sexId_toElement`) — the same endomap, named once in each morphism language.

**Axioms.** Object-level neighbourhood / ideal isos, `sexDomainEquationIso`, and
Factoid 4.6 for `idMap` audit to `{propext, Classical.choice, Quot.sound}` through
the InfoSys/`Finset` frontier of §4. The uncompared semantic factor
`sexRhsSemanticIso` additionally uses the 1982 sum trichotomy.

**Lean 4**

- [BridgeTheorems/TreeProd.lean](TreeProd.lean)
- [BridgeTheorems/WorkedExampleSExpr/lowerBoundSystem.lean](WorkedExampleSExpr/lowerBoundSystem.lean)
- [BridgeTheorems/WorkedExampleSExpr/SexSys.lean](WorkedExampleSExpr/SexSys.lean)
- [BridgeTheorems/WorkedExampleSExpr/SexRhs.lean](WorkedExampleSExpr/SexRhs.lean)
- [BridgeTheorems/WorkedExampleSExpr/sexAtom.lean](WorkedExampleSExpr/sexAtom.lean)
- [BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso.lean](WorkedExampleSExpr/sexDomainEquationIso.lean)
- [BridgeTheorems/WorkedExampleSExpr/sexRhsSemanticIso.lean](WorkedExampleSExpr/sexRhsSemanticIso.lean)
- [BridgeTheorems/WorkedExampleSExpr/Basic.lean](WorkedExampleSExpr/Basic.lean)
- [BridgeTheorems/WorkedExampleSExpr/exists_sexDomainEquationIso.lean](WorkedExampleSExpr/exists_sexDomainEquationIso.lean)
- [BridgeTheorems/WorkedExampleSExpr/exists_sexIdealIso.lean](WorkedExampleSExpr/exists_sexIdealIso.lean)
- [BridgeTheorems/WorkedExampleSExpr/exists_sexNeighborhoodIso.lean](WorkedExampleSExpr/exists_sexNeighborhoodIso.lean)
- [BridgeTheorems/WorkedExampleSExpr/sexAtom_mem_self.lean](WorkedExampleSExpr/sexAtom_mem_self.lean)
- [BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_fold.lean](WorkedExampleSExpr/sexDomainEquationIso_fold.lean)
- [BridgeTheorems/WorkedExampleSExpr/sexDomainEquationIso_unfold.lean](WorkedExampleSExpr/sexDomainEquationIso_unfold.lean)
- [BridgeTheorems/WorkedExampleSExpr/sexId_toElement.lean](WorkedExampleSExpr/sexId_toElement.lean)
- [BridgeTheorems/WorkedExampleSExpr/sexRhs_eq_sum_product.lean](WorkedExampleSExpr/sexRhs_eq_sum_product.lean)
- [BridgeTheorems/WorkedExampleSExpr/sexUnfold_atom.lean](WorkedExampleSExpr/sexUnfold_atom.lean)
- [BridgeTheorems/WorkedExampleSExpr.lean](WorkedExampleSExpr.lean)
- [BridgeTheorems/treeFold.lean](treeFold.lean)
- [BridgeTheorems/treeFold_eq_or_pairBots.lean](treeFold_eq_or_pairBots.lean)
- [BridgeTheorems/treeUnfold_treeFold.lean](treeUnfold_treeFold.lean)
- [BridgeTheorems/unfoldInsert.lean](unfoldInsert.lean)
- [BridgeTheorems/SexDomainEquationInst10.lean](SexDomainEquationInst10.lean)
- [BridgeTheorems/foldInsert.lean](foldInsert.lean)
- [BridgeTheorems/SexDomainEquationInst15.lean](SexDomainEquationInst15.lean)
- [BridgeTheorems/TreeEnt_pairL_bot_of_pairs.lean](TreeEnt_pairL_bot_of_pairs.lean)
- [BridgeTheorems/TreeEnt_pairR_bot_of_pairs.lean](TreeEnt_pairR_bot_of_pairs.lean)
- [BridgeTheorems/foldFinset.lean](foldFinset.lean)
- [BridgeTheorems/mem_closed_pair_bots.lean](mem_closed_pair_bots.lean)
- [BridgeTheorems/saturated_of_closed.lean](saturated_of_closed.lean)
- [BridgeTheorems/mem_foldr_fold.lean](mem_foldr_fold.lean)
- [BridgeTheorems/mem_foldFinset.lean](mem_foldFinset.lean)
- [BridgeTheorems/mem_foldr_unfold.lean](mem_foldr_unfold.lean)
- [BridgeTheorems/unfoldFinset.lean](unfoldFinset.lean)
- [BridgeTheorems/mem_unfoldFinset.lean](mem_unfoldFinset.lean)
- [BridgeTheorems/lftFinset_image_unfold.lean](lftFinset_image_unfold.lean)
- [BridgeTheorems/rhtFinset_image_unfold_mem.lean](rhtFinset_image_unfold_mem.lean)
- [BridgeTheorems/SumCon_image_treeCon.lean](SumCon_image_treeCon.lean)
- [BridgeTheorems/SumEnt_treeFold.lean](SumEnt_treeFold.lean)
- [BridgeTheorems/TreeCon_image_sumCon.lean](TreeCon_image_sumCon.lean)
- [BridgeTheorems/TreeEnt_sumEnt.lean](TreeEnt_sumEnt.lean)
- [BridgeTheorems/foldElement.lean](foldElement.lean)
- [BridgeTheorems/unfoldFinset_foldFinset.lean](unfoldFinset_foldFinset.lean)
- [BridgeTheorems/unfoldElement.lean](unfoldElement.lean)
- [BridgeTheorems/foldElement_unfoldElement.lean](foldElement_unfoldElement.lean)
- [BridgeTheorems/unfoldElement_foldElement.lean](unfoldElement_foldElement.lean)
- [BridgeTheorems/treeDomainIso.lean](treeDomainIso.lean)
- [BridgeTheorems/SexDomainEquation.lean](SexDomainEquation.lean)
- [BridgeTheorems.lean](../BridgeTheorems.lean)
