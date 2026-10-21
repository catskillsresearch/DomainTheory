/-ai
If a Scott-continuous map lies above a set x, the least upper bound of the iterates above x is a fixed point.

The chain lemma rewrites the image of the union as the union of the successor iterates. An element of a successor iterate lies in the full union one index later. Conversely, an element of the starting iterate lies in the image by the hypothesis that the starting set lies below its image, and an element of a successor iterate is already a member of that same summand of the image union.
ai-/
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
