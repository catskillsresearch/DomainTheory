module
public import DomainTheory.ContinuousLattice.ContinuousLattices.idemFix_scottTopology
public import DomainTheory.ContinuousLattice.ContinuousLattices.idemFix_isContinuousLattice
public import DomainTheory.ContinuousLattice.Constructions.sierpinskiPower_isContinuousLattice
public import DomainTheory.ContinuousLattice.Constructions.scottTopology_sierpinskiPower
public import DomainTheory.ContinuousLattice.Injective.corollary_1_6
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_preservesDirectedSup
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import Mathlib.Data.Set.Basic
public import Mathlib.Topology.Defs.Basic


@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set


universe u

/-- **Scott 1972, Theorem 2.12 (backward direction).** Every injective `T₀`-space is homeomorphic
to a continuous lattice equipped with its Scott topology.

The injective space `D` is a retract of a power `𝕆^I = (I → Prop)` of the Sierpiński space
(Corollary 1.6). Writing `s : D → 𝕆^I` for the embedding and `r : 𝕆^I → D` for the retraction,
`e := s ∘ r` is a Scott-continuous idempotent on `𝕆^I` (its topology is its Scott topology by
`scottTopology_sierpinskiPower`). The fixed-point set `IdemFix e` is therefore a continuous lattice
(`idemFix_isContinuousLattice`, via Proposition 2.10), and `d ↦ s d` is a homeomorphism `D ≃ₜ
IdemFix e` with inverse the retraction. -/
theorem theorem_2_12_backward {D : Type u} [TopologicalSpace D] [T0Space D]
    (hD : InjectiveSpace.{u, u} D) :
    ∃ (E : Type u) (inst : CompleteLattice E),
      @ContinuousLattice E inst ∧
        Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by
  obtain ⟨ι, ⟨R⟩⟩ := (corollary_1_6 D).1 hD
  -- `e = s ∘ r` on the Sierpiński power `L = ι → Prop`.
  have hidem : ∀ x, R.section' (R.retraction (R.section' (R.retraction x)))
      = R.section' (R.retraction x) :=
    fun x => congrArg R.section' (R.retraction_section (R.retraction x))
  have hL : ContinuousLattice (ι → Prop) := sierpinskiPower_isContinuousLattice ι
  -- `e` is Scott-continuous: it is product-continuous (`s ∘ r`), and the Scott topology of the
  -- Sierpiński power is its product topology.
  have hcont_e : @Continuous (ι → Prop) (ι → Prop) scottTopologicalSpace scottTopologicalSpace
      (fun x => R.section' (R.retraction x)) := by
    rw [scottTopology_sierpinskiPower ι]
    exact R.section'.continuous.comp R.retraction.continuous
  have hsc : PreservesDirectedSup (fun x => R.section' (R.retraction x)) :=
    continuous_preservesDirectedSup hcont_e
  refine ⟨IdemFix (fun x => R.section' (R.retraction x)),
    IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc),
    idemFix_isContinuousLattice hidem hsc hL, ?_⟩
  -- The Scott topology of `IdemFix e` equals the subspace topology it inherits as a subtype of the
  -- Sierpiński power: both are `induced Subtype.val` of the (Scott = product) topology of `𝕆^I`.
  have heq : (@scottTopologicalSpace (IdemFix (fun x => R.section' (R.retraction x)))
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)))
      = instTopologicalSpaceSubtype := by
    rw [idemFix_scottTopology hidem hsc hL, scottTopology_sierpinskiPower ι]
    rfl
  rw [heq]
  -- the homeomorphism `D ≃ₜ IdemFix e`, with the subspace topology (where `Continuous.comp` works)
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
