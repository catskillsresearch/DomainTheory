/-ai
Every element u of Pω is contained in the conditional of u on the singleton {0} and on ⊤ + 1.

If 0 belongs to u, the zero clause of the conditional returns it. If a successor k + 1 belongs to u, then k belongs to ⊤, so the successor clause of the conditional returns k + 1.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
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
