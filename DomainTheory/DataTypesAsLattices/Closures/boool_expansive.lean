
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boool_expansive (u : Pomega) :
    u ⊆ condSet u (ofNat 0) (succSet topElem) := by
  intro k hk
  cases k with
  | zero => exact Or.inl ⟨rfl, hk⟩
  | succ k => exact Or.inr ⟨⟨k, Set.mem_univ k, rfl⟩, ⟨k, hk⟩⟩

end DomainTheory.DataTypesAsLattices
