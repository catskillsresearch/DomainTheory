/-ai
Z belongs to the two-variable action of fade₂ on t and y if and only if Z is a D-neighbourhood and either Z is the master or t contains {0} and y contains Z.

A witnessing pair of neighbourhoods gives either Z equal to the master, or an input equal to {0} belonging to t together with an output contained in Z and belonging to y. Conversely, the two masters witness the master case, and the pair consisting of {0} and Z witnesses the other case.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fade₂
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fade

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

/-- The closed form of `fade`'s elementwise action on a pair `⟨t, y⟩`: `fade(t,y) ∋ Z ↔ Z = Δ_D ∨
(t ∋ {0} ∧ y ∋ Z)`. -/
theorem mem_toElementMap₂_fade (t : O.Element) (y : D.Element) {Z : Set α} :
    (fade₂.toElementMap₂ t y).mem Z ↔
      D.mem Z ∧ (Z = D.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ y.mem Z)) := by
  rw [mem_toElementMap₂]
  constructor
  · rintro ⟨X, Y, htX, hyY, hXO, hYD, hZD, hcase⟩
    refine ⟨hZD, ?_⟩
    rcases hcase with h | ⟨hXeq, hYZ⟩
    · exact Or.inl h
    · exact Or.inr ⟨hXeq ▸ htX, y.up_mem hyY hZD hYZ⟩
  · rintro ⟨hZD, hZeq | ⟨ht0, hyZ⟩⟩
    · exact ⟨O.master, D.master, t.master_mem, y.master_mem, O.master_mem, D.master_mem, hZD,
        Or.inl hZeq⟩
    · exact ⟨({0} : Set (Fin 2)), Z, ht0, hyZ, O_mem_zero, hZD, hZD, Or.inr ⟨rfl, subset_rfl⟩⟩

end DomainTheory.NeighbourhoodSystems
