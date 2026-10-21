/-ai
If a tree token lies in a tree-system element, then the fold of its unfold also lies in that element.

Either the fold of the unfold equals the token, or the token is pair-right of bottom and the fold of its unfold is pair-left of bottom. In the first case the hypothesis applies. In the second, the two pair-bottom tokens belong to an element together.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.treeFold_eq_or_pairBots
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.mem_closed_pair_bots

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem saturated_of_closed (x : (treeSystem A).Element) {t : TreeToken α}
    (ht : t ∈ x.carrier) : treeFold A (treeUnfold A t) ∈ x.carrier := by
  rcases treeFold_eq_or_pairBots A t with h | ⟨rfl, hf⟩
  · rwa [h]
  · rw [hf]
    exact (mem_closed_pair_bots A x).2 ht

end DomainTheory.BridgeTheorems
