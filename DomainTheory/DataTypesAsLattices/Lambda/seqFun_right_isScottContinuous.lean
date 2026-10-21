/-ai
For each element u of Pω, the map sending x to the sequence revaluation of u along the members of x is Scott continuous.

Fix x and a natural number k. If k lies in the union of the values of u at the numerals of members of x, the witness index i has the singleton coded by 2^i contained in x, and k lies in that Scott piece of the union. Conversely, membership in the Scott union supplies a code whose finite set is contained in x together with a witness index in that finite set; the same index still lies in x, so k lies in the original union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seqFun_right_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x => seqFun u x) := by
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ i, by simp [e_pow2, Set.singleton_subset_iff, hi],
      Set.mem_iUnion₂.mpr ⟨i, by simp [e_pow2], hki⟩⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hkn
    exact Set.mem_iUnion₂.mpr ⟨i, hn hi, hki⟩

end DomainTheory.DataTypesAsLattices
