
module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_zero
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_one
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset
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
        (funOf.isScottContinuous_left (ofNat 0)) hf,
      theorem_1_3 (f := fun u => funOf u (ofNat 1))
        (funOf.isScottContinuous_left (ofNat 1)) hf, rfl⟩

end DomainTheory.DataTypesAsLattices
