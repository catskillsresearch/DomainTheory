module

public import DomainTheory.ContinuousLattice.Constructions.scottTopology
public import DomainTheory.ContinuousLattice.ContinuousLattices.IdempotentFixedPoint.scottContinuous
public import DomainTheory.ContinuousLattice.Injective.corollary_1_6

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

/-- An injective `T₀` space is homeomorphic to a continuous lattice under its Scott topology. -/
theorem injective_homeomorph_to_continuousLatticeScott {D : Type u} [TopologicalSpace D]
    [T0Space D] (hD : InjectiveSpace.{u, u} D) :
    ∃ (E : Type u) (inst : CompleteLattice E),
      @ContinuousLattice E inst ∧
        Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by
  obtain ⟨ι, ⟨R⟩⟩ := (corollary_1_6 D).1 hD

  have hidem : ∀ x, R.section' (R.retraction (R.section' (R.retraction x)))
      = R.section' (R.retraction x) :=
    fun x => congrArg R.section' (R.retraction_section (R.retraction x))
  have hL : ContinuousLattice (ι → Prop) := proposition_2_9.sierpinskiPower ι

  have hcont_e : @Continuous (ι → Prop) (ι → Prop) scottTopologicalSpace scottTopologicalSpace
      (fun x => R.section' (R.retraction x)) := by
    rw [scottTopology.sierpinskiPower ι]
    exact R.section'.continuous.comp R.retraction.continuous
  have hsc : PreservesDirectedSup (fun x => R.section' (R.retraction x)) :=
    continuous_preservesDirectedSup hcont_e
  refine ⟨IdempotentFixedPoint (fun x => R.section' (R.retraction x)),
    IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc),
    IdempotentFixedPoint.isContinuousLattice hidem hsc hL, ?_⟩

  have heq : (@scottTopologicalSpace (IdempotentFixedPoint (fun x => R.section' (R.retraction x)))
      (IdempotentFixedPoint.completeLattice hidem (preservesDirectedSup_monotone hsc)))
      = instTopologicalSpaceSubtype := by
    rw [IdempotentFixedPoint.scottTopology hidem hsc hL, scottTopology.sierpinskiPower ι]
    rfl
  rw [heq]

  have hfix : ∀ d, (fun x => R.section' (R.retraction x)) (R.section' d) = R.section' d :=
    fun d => congrArg R.section' (R.retraction_section d)
  exact ⟨{
    toFun := fun d => ⟨R.section' d, hfix d⟩
    invFun := fun k => R.retraction k.1
    left_inv := fun d => R.retraction_section d
    right_inv := fun k => Subtype.ext k.2
    continuous_toFun := by exact R.section'.continuous.subtype_mk hfix
    continuous_invFun := by exact R.retraction.continuous.comp continuous_subtype_val }⟩

end DomainTheory.ContinuousLattice
