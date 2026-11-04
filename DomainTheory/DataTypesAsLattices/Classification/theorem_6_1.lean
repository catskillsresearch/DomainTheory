module

public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
import DomainTheory.DataTypesAsLattices.Classification.CharacteristicMaps
import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

theorem theorem_6_1 :
    (∀ f : Pomega → Pomega, IsScottContinuous f →
        IsScottOpen {x | 0 ∈ f x}) ∧
      (∀ U, IsScottOpen U →
        ∃ f, IsScottContinuous f ∧ U = {x | 0 ∈ f x}) := by
  constructor
  · intro f hf
    refine ⟨{n | 0 ∈ f (e n)}, ?_⟩
    ext x
    constructor
    · intro hx
      have : 0 ∈ scottUnion f x := by rwa [← hf.out x]
      obtain ⟨n, hn, h0⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, h0, hn⟩
    · intro hx
      obtain ⟨n, h0, hn⟩ := Set.mem_iUnion₂.mp hx
      exact IsScottContinuous.monotone hf hn h0
  · intro U hU
    refine ⟨charOpen U, charOpen.isScottContinuous U, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨B, rfl⟩ := hU
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      refine ⟨rfl, n, hxn, ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩
    · intro ⟨_, n, hn, hne⟩
      exact isScottOpen_isUpper hU hne hn

end DomainTheory.DataTypesAsLattices
