module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.iterateFrom
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove
public import DomainTheory.DataTypesAsLattices.Retracts.iterateFrom_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem lfpAbove_fixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (hx : x ⊆ f x) : f (lfpAbove f x) = lfpAbove f x := by
  have hchain := chain_lemma hf (iterateFrom f x) (iterateFrom_mono hf hx)
  unfold lfpAbove
  rw [hchain]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n + 1, hkn⟩
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    cases n with
    | zero => exact Set.mem_iUnion.mpr ⟨0, hx hkn⟩
    | succ n => exact Set.mem_iUnion.mpr ⟨n, hkn⟩

end DomainTheory.DataTypesAsLattices
