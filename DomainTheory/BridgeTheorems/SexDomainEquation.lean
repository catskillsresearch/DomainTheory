module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.unfoldInsert
public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.foldInsert
public import DomainTheory.BridgeTheorems.foldFinset
public import DomainTheory.BridgeTheorems.unfoldElement
public import DomainTheory.BridgeTheorems.foldElement
public import DomainTheory.BridgeTheorems.treeDomainIso
public import DomainTheory.BridgeTheorems.TreeProd
public import DomainTheory.BridgeTheorems.treeUnfold_treeFold
public import DomainTheory.BridgeTheorems.treeFold_eq_or_pairBots
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.mem_foldr_unfold
public import DomainTheory.BridgeTheorems.mem_unfoldFinset
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.mem_foldr_fold
public import DomainTheory.BridgeTheorems.mem_foldFinset
public import DomainTheory.BridgeTheorems.unfoldFinset_foldFinset
public import DomainTheory.BridgeTheorems.lftFinset_image_unfold
public import DomainTheory.BridgeTheorems.rhtFinset_image_unfold_mem
public import DomainTheory.BridgeTheorems.TreeCon_image_sumCon
public import DomainTheory.BridgeTheorems.SumCon_image_treeCon
public import DomainTheory.BridgeTheorems.TreeEnt_sumEnt
public import DomainTheory.BridgeTheorems.SumEnt_treeFold
public import DomainTheory.BridgeTheorems.TreeEnt_pairL_bot_of_pairs
public import DomainTheory.BridgeTheorems.TreeEnt_pairR_bot_of_pairs
public import DomainTheory.BridgeTheorems.mem_closed_pair_bots
public import DomainTheory.BridgeTheorems.saturated_of_closed
public import DomainTheory.BridgeTheorems.unfoldElement_foldElement
public import DomainTheory.BridgeTheorems.foldElement_unfoldElement

@[expose] public section

/-!
# Domain equation `|T| ≃o |A + (T × T)|` via unfolding

Factoid 8.1 presents `T` as an inductive token system whose official
right-hand side is `sumSystem A (productSystem T T)`. The token map
`treeUnfold` is a retraction, identifying only Scott’s two encodings of
the product bottom (`pairL Δ` and `pairR Δ`). After the matching
`ent_bot` clauses, closed elements are saturated for that kernel, so
image and preimage of `treeUnfold` are inverse order isomorphisms of
domains.
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)































end DomainTheory.BridgeTheorems
