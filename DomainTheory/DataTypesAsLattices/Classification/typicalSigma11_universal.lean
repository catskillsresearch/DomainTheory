/-ai
Scott's Table 3 states that Σ₁¹ is the class of continuous preimages of the set of u such that u applied to {0} and u applied to {1} agree at some common argument.

If U is the set of x at which two Scott-continuous maps agree somewhere, the pairing of those two values is Scott continuous in x, and the evaluations of the pairing at {0} and at {1} put the pairing in the typical set exactly on U. Conversely, if U is the preimage of the typical set under a Scott-continuous map f, the two maps sending x to f(x) applied to {0} and to f(x) applied to {1} are Scott continuous by the composition theorem, and their agreement set is U.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Table 3.** `Σ₁¹` is the class of continuous preimages of
`{u | ∃ y. u₀(y) = u₁(y)}`. -/
theorem typicalSigma11_universal (U : Set Pomega) :
    IsSigma11 U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalSigma11} := by
  constructor
  · rintro ⟨f, g, hf, hg, rfl⟩
    refine ⟨fun x => seq2 (f x) (g x), seq2_pair_isScottContinuous hf hg, ?_⟩
    ext x
    constructor
    · intro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simpa [seq2_app_zero, seq2_app_one] using hy
    · intro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simpa [seq2_app_zero, seq2_app_one] using hy
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun x => funOf (f x) (ofNat 0), fun x => funOf (f x) (ofNat 1),
      theorem_1_3 (f := fun u => funOf u (ofNat 0))
        (funOf_isScottContinuous_left (ofNat 0)) hf,
      theorem_1_3 (f := fun u => funOf u (ofNat 1))
        (funOf_isScottContinuous_left (ofNat 1)) hf, rfl⟩

end DomainTheory.DataTypesAsLattices
