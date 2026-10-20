/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product

public import DomainTheory.InformationSystems.Factoid83.VToken
public import DomainTheory.InformationSystems.Factoid83.VEnt
import all DomainTheory.InformationSystems.Factoid83.VEnt
public import DomainTheory.InformationSystems.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.Factoid83.vBot
public import DomainTheory.InformationSystems.Factoid83.vTop
public import DomainTheory.InformationSystems.Factoid83.VCon
public import DomainTheory.InformationSystems.Factoid83.vSystem
public import DomainTheory.InformationSystems.Factoid83.vUnfold
public import DomainTheory.InformationSystems.Factoid83.vRhs
public import DomainTheory.InformationSystems.Factoid83.IsUToken
public import DomainTheory.InformationSystems.Factoid83.UToken
public import DomainTheory.InformationSystems.Factoid83.uBot
public import DomainTheory.InformationSystems.Factoid83.uForget
public import DomainTheory.InformationSystems.Factoid83.uForgetInsert
public import DomainTheory.InformationSystems.Factoid83.uForgetFinset
public import DomainTheory.InformationSystems.Factoid83.UCon
public import DomainTheory.InformationSystems.Factoid83.UEnt
public import DomainTheory.InformationSystems.Factoid83.uSystem
public import DomainTheory.InformationSystems.Factoid83.mem_vPairLFinset
public import DomainTheory.InformationSystems.Factoid83.mem_vPairRFinset
public import DomainTheory.InformationSystems.Factoid83.vPairLFinset_empty
public import DomainTheory.InformationSystems.Factoid83.vPairLFinset_mono
public import DomainTheory.InformationSystems.Factoid83.vPairRFinset_mono
public import DomainTheory.InformationSystems.Factoid83.vPairLFinset_insert_pairL
public import DomainTheory.InformationSystems.Factoid83.vPairRFinset_insert_pairR
public import DomainTheory.InformationSystems.Factoid83.vPairLFinset_insert_bot
public import DomainTheory.InformationSystems.Factoid83.vPairRFinset_insert_bot
public import DomainTheory.InformationSystems.Factoid83.vPairLFinset_insert_pairR
public import DomainTheory.InformationSystems.Factoid83.vPairRFinset_insert_pairL
public import DomainTheory.InformationSystems.Factoid83.VEnt_of_ent_top
public import DomainTheory.InformationSystems.Factoid83.VEnt_mono
public import DomainTheory.InformationSystems.Factoid83.VEnt_of_mem
public import DomainTheory.InformationSystems.Factoid83.not_VEnt_empty_top
public import DomainTheory.InformationSystems.Factoid83.VEnt_pairL_inv
public import DomainTheory.InformationSystems.Factoid83.VEnt_pairR_inv
public import DomainTheory.InformationSystems.Factoid83.VEnt_pairLFinset_of_EntSet
public import DomainTheory.InformationSystems.Factoid83.VEnt_pairRFinset_of_EntSet
public import DomainTheory.InformationSystems.Factoid83.VEnt_trans
public import DomainTheory.InformationSystems.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.Factoid83.mem_foldr_uForget
public import DomainTheory.InformationSystems.Factoid83.mem_uForgetFinset
public import DomainTheory.InformationSystems.Factoid83.uForgetFinset_singleton
public import DomainTheory.InformationSystems.Factoid83.uForgetFinset_insert
public import DomainTheory.InformationSystems.Factoid83.uForgetFinset_mono
public import DomainTheory.InformationSystems.Factoid83.not_VEnt_singleton_ne_top
public import DomainTheory.InformationSystems.Factoid83.UCon_singleton
public import DomainTheory.InformationSystems.Factoid83.UCon_subset
public import DomainTheory.InformationSystems.Factoid83.VEnt_insert_top_imp
public import DomainTheory.InformationSystems.Factoid83.not_VEnt_insert_top_of_ent
public import DomainTheory.InformationSystems.Factoid83.UCon_insert_of_ent
public import DomainTheory.InformationSystems.Factoid83.UEnt_bot
public import DomainTheory.InformationSystems.Factoid83.UEnt_of_mem
public import DomainTheory.InformationSystems.Factoid83.UEnt_trans

@[expose] public section

/-!
# Factoid 8.3 — universal domain via `V` (with top) and `U` (top removed)

**Scott 1982, §8.** Construct `V` with bottom `Δ` and top `∇`, close under product
flavours `(X, Δ)` / `(Δ, Y)`, take all finite sets consistent, and define entailment
by Scott’s clauses (3)–(6). Then form `U` by deleting `∇` and retaining only those
finite sets that do not entail `∇` (clauses (7)–(10)).

The retract/universality theorem (every countably based domain is a retract of `U`)
is stated by Scott without proof here; we package `vSystem` / `uSystem` and the
domain equation `V ≅ V × V` on the product-shaped tokens.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-! ## Tokens of `V` (Scott (1)–(2)) -/



/-! ## Projections `{X | (X,Δ) ∈ u}` and `{Y | (Δ,Y) ∈ u}` -/













/-! ## Entailment for `V` (Scott (3)–(6)); all finite sets consistent -/












/-! ## Domain equation `V ≅ V × V` (product-shaped tokens) -/



/-! ## The universal domain `U` (Scott (7)–(10)) -/


























end InfoSys
end DomainTheory.InformationSystems
