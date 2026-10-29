module

public import DomainTheory.ContinuousLattice.Constructions.proposition_2_9
public import DomainTheory.ContinuousLattice.Constructions.proposition_2_11
public import DomainTheory.ContinuousLattice.Constructions.scottTopology
public import DomainTheory.ContinuousLattice.ContinuousLattices.IdemFix
public import DomainTheory.ContinuousLattice.ContinuousLattices.orderIsoScottHomeomorph
public import DomainTheory.ContinuousLattice.Injective.corollary_1_6
public import DomainTheory.ContinuousLattice.Injective.proposition_1_2
public import DomainTheory.ContinuousLattice.Injective.proposition_1_4
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_preservesDirectedSup
public import DomainTheory.ContinuousLattice.Specialization.SpecializationPreorder

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

namespace theorem_2_12

theorem backward {D : Type u} [TopologicalSpace D] [T0Space D]
    (hD : InjectiveSpace.{u, u} D) :
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
  refine ⟨IdemFix (fun x => R.section' (R.retraction x)),
    IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc),
    IdemFix.isContinuousLattice hidem hsc hL, ?_⟩

  have heq : (@scottTopologicalSpace (IdemFix (fun x => R.section' (R.retraction x)))
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)))
      = instTopologicalSpaceSubtype := by
    rw [IdemFix.scottTopology hidem hsc hL, scottTopology.sierpinskiPower ι]
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

theorem backward_exact {A : Type u} [latticeA : CompleteLattice A] [τA : TopologicalSpace A]
    [T0Space A] (hA : InjectiveSpace.{u, u} A)
    (hspec : ∀ x y : A, SpecializationPreorder x y ↔ @LE.le A latticeA.toLE x y) :
    ContinuousLattice A ∧
      (@scottTopologicalSpace A latticeA) = τA := by
  obtain ⟨E, instE, hE, ⟨h⟩⟩ := backward hA
  let : CompleteLattice E := instE
  let : TopologicalSpace E := @scottTopologicalSpace E instE
  let : Preorder A := latticeA.toPreorder
  let : Preorder E := instE.toPreorder
  let e : A ≃o E := h.toEquiv.toOrderIso
    (fun x y hxy => by
      exact SpecializationPreorder.scott_iff.mp
        (SpecializationPreorder.map ((hspec x y).mpr hxy) h.continuous))
    (fun x y hxy => by
      exact (hspec (h.symm x) (h.symm y)).mp
        (SpecializationPreorder.map (SpecializationPreorder.scott_iff.mpr hxy) h.symm.continuous))
  have hcont : ContinuousLattice A := ContinuousLattice.orderIso e hE
  refine ⟨hcont, ?_⟩
  have heqOrder :
      (@scottTopologicalSpace A latticeA) =
        TopologicalSpace.induced (e : A → E) (@scottTopologicalSpace E instE) := by
    let : TopologicalSpace A := @scottTopologicalSpace A latticeA
    exact (@orderIsoScottHomeomorph A E latticeA instE e).isInducing.eq_induced
  have heqHome :
      τA = TopologicalSpace.induced (h : A → E) (@scottTopologicalSpace E instE) :=
    (@Homeomorph.isInducing A E τA (@scottTopologicalSpace E instE) h).eq_induced
  exact heqOrder.trans heqHome.symm

theorem forward {E : Type*} [CompleteLattice E] (hE : ContinuousLattice E) :
    @InjectiveSpace E scottTopologicalSpace :=
  proposition_2_11 hE

theorem injective_half : InjectiveSpace Prop :=
  proposition_1_2

theorem sierpinski_backward (_h : ContinuousLattice Prop) : InjectiveSpace Prop :=
  proposition_1_2

end theorem_2_12

theorem theorem_2_12 {D : Type u} [TopologicalSpace D] [T0Space D] :
    InjectiveSpace.{u, u} D ↔
      ∃ (E : Type u) (inst : CompleteLattice E),
        @ContinuousLattice E inst ∧
          Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by
  refine ⟨theorem_2_12.backward, ?_⟩
  rintro ⟨E, inst, hE, ⟨h⟩⟩
  let τE : TopologicalSpace E := @scottTopologicalSpace E inst
  exact @proposition_1_4 E D τE _ (theorem_2_12.forward hE)
    ⟨⇑h, h.continuous⟩ ⟨⇑h.symm, h.symm.continuous⟩ (fun d => h.left_inv d)

end DomainTheory.ContinuousLattice
