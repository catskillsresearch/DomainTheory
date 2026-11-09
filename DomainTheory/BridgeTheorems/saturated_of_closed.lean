module

public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Element
public import DomainTheory.BridgeTheorems.mem_closed_pair_bots
public import DomainTheory.BridgeTheorems.treeFold_eq_or_pairBots

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys
open treeSystem

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem saturated_of_closed (x : (treeSystem A).Element) {t : TreeToken α}
    (ht : t ∈ x.carrier) : treeFold A (treeUnfold A t) ∈ x.carrier := by
  rcases treeFold_eq_or_pairBots A t with h | ⟨rfl, hf⟩
  · rwa [h]
  · rw [hf]
    exact (mem_closed_pair_bots A x).2 ht

end DomainTheory.BridgeTheorems
