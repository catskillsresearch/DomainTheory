/-ai
Applying the sequence shift of u to the numeral i equals applying u to the numeral i + 1.

Rewrite by the application law for the shift. A member of the resulting union is indexed by an element of the successor of the numeral i, and that index is i + 1, so the membership is membership in the application of u to the numeral i + 1. Conversely, i + 1 is the successor of i, and the same membership exhibits it in the union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seqShift_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seqShift_ofNat (u : Pomega) (i : ℕ) :
    funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
  rw [seqShift_app]
  ext m
  constructor
  · intro hm
    obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
    simp [succSet, ofNat] at hj; subst hj; exact hmj
  · intro hm
    exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩

end DomainTheory.DataTypesAsLattices
