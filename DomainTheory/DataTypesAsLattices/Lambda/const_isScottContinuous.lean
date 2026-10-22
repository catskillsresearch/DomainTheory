/-ai
A constant map on Pω is Scott continuous.

Membership in the constant value is witnessed in the Scott union by the empty finite set, and every Scott-union witness already lies in that value.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem const_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun _ : Pomega => c) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    exact mem_scottUnion.mpr ⟨0, by simp [e_zero], hk⟩
  · intro hk
    obtain ⟨_, _, hkn⟩ := mem_scottUnion.mp hk
    exact hkn

end DomainTheory.DataTypesAsLattices
