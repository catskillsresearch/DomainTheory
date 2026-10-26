module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.openR
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.openR_app
public import DomainTheory.DataTypesAsLattices.Closures.openR_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem openR_idem (u : Pomega) :
    funOf openR (funOf openR u) = funOf openR u := by
  apply subset_antisymm
  · intro m hm
    rw [openR_app] at hm ⊢
    obtain ⟨n, hn, hnu⟩ := hm
    rw [openR_app] at hnu
    obtain ⟨k, hk, hku⟩ := hnu
    exact ⟨k, subset_trans hk hn, hku⟩
  · exact openR_expansive (funOf openR u)

end DomainTheory.DataTypesAsLattices
