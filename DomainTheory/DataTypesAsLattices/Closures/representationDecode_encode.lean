module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem representationDecode_encode
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) (x : α) :
    representationDecode D (representationEncode D x) = x := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨n, hn, rfl⟩
    exact hn
  · calc
      x = sSup {k : α | IsCompact k ∧ k ≤ x} := D.density x
      _ ≤ representationDecode D (representationEncode D x) := by
        apply sSup_le
        rintro k ⟨hkc, hkx⟩
        obtain ⟨n, rfl⟩ := D.compact_complete k hkc
        exact le_sSup ⟨n, hkx, rfl⟩

end DomainTheory.DataTypesAsLattices
