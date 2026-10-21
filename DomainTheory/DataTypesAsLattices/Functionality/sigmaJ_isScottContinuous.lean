/-ai
The independent successor σ_j is Scott continuous.

Extensionality matches membership in σ_j(x) with membership in the Scott union of the images of the finite approximants. If the code of (j, k) lies in x, the finite approximant given by the power of two at that code lies below x, and the same index witnesses the successor code in the image of that approximant. Conversely, a finite approximant below x and a witness index return that pair code as an element of x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sigmaJ_isScottContinuous (j : ℕ) : IsScottContinuous (sigmaJ j) := by
  intro x
  ext p
  constructor
  · intro ⟨k, heq, hp⟩
    refine mem_scottUnion.mpr ⟨2 ^ pair j k, ?_, k, heq, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff] using hp
    · simp [e_pow2]
  · intro hp
    obtain ⟨n, hn, k, heq, hpk⟩ := mem_scottUnion.mp hp
    exact ⟨k, heq, hn hpk⟩

end DomainTheory.DataTypesAsLattices
