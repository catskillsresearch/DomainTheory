module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.PolymorphicType

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

noncomputable def piU (d : ApproximableMap U U) : ApproximableMap U U :=
  iArrow.comp ((piD d).comp jArrow)

namespace toElementMap

theorem piU (d : ApproximableMap U U) (w : U.Element) :
    (DomainTheory.NeighbourhoodSystems.piU d).toElementMap w =
      iArrow.toElementMap ((piD d).toElementMap (jArrow.toElementMap w)) := by
  unfold DomainTheory.NeighbourhoodSystems.piU
  rw [toElementMap_comp, toElementMap_comp]

end toElementMap

namespace piD

theorem fix_of_piU_fix {d : ApproximableMap U U} {w : U.Element}
    (hw : (piU d).toElementMap w = w) :
    (piD d).toElementMap (jArrow.toElementMap w) = jArrow.toElementMap w := by
  rw [toElementMap.piU] at hw
  have hstep := congrArg jArrow.toElementMap hw
  rwa [jArrow_comp_iArrow_apply] at hstep

end piD

namespace piU

theorem fix_of_piD_fix {d : ApproximableMap U U} {φ : (funSpace U U).Element}
    (hφ : (piD d).toElementMap φ = φ) :
    (piU d).toElementMap (iArrow.toElementMap φ) = iArrow.toElementMap φ := by
  rw [toElementMap.piU, jArrow_comp_iArrow_apply, hφ]

noncomputable def FixIso (d : ApproximableMap U U) :
    {w : U.Element // (piU d).toElementMap w = w} ≃o
      {φ : (funSpace U U).Element // (piD d).toElementMap φ = φ} where
  toFun w := ⟨jArrow.toElementMap w.1, piD.fix_of_piU_fix w.2⟩
  invFun φ := ⟨iArrow.toElementMap φ.1, fix_of_piD_fix φ.2⟩
  left_inv w := by
    apply Subtype.ext
    show iArrow.toElementMap (jArrow.toElementMap w.1) = w.1
    have hw := toElementMap.piU d w.1
    rw [w.2] at hw
    rw [piD.fix_of_piU_fix w.2] at hw
    exact hw.symm
  right_inv φ := by
    apply Subtype.ext
    exact jArrow_comp_iArrow_apply φ.1
  map_rel_iff' := by
    intro w w'
    show jArrow.toElementMap w.1 ≤ jArrow.toElementMap w'.1 ↔ w.1 ≤ w'.1
    constructor
    · intro hle
      have h2 := iArrow.toElementMap_mono hle
      have e1 : iArrow.toElementMap (jArrow.toElementMap w.1) = w.1 := by
        have hw := toElementMap.piU d w.1
        rw [w.2, piD.fix_of_piU_fix w.2] at hw
        exact hw.symm
      have e2 : iArrow.toElementMap (jArrow.toElementMap w'.1) = w'.1 := by
        have hw' := toElementMap.piU d w'.1
        rw [w'.2, piD.fix_of_piU_fix w'.2] at hw'
        exact hw'.symm
      rwa [e1, e2] at h2
    · intro hle
      exact jArrow.toElementMap_mono hle

end piU

namespace isFinitary

theorem piU_of_isFinitary_piD {d : ApproximableMap U U} (h : IsFinitary (piD d)) :
    IsFinitary (piU d) := by
  obtain ⟨β, F, ⟨iso⟩⟩ := h
  exact ⟨β, F, ⟨(piU.FixIso d).trans iso⟩⟩

theorem piU_of_formula {d : ApproximableMap U U}
    (hii : ∀ (x : (funSpace U U).Element) {Y}, ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) :
    IsFinitary (piU d) :=
  piU_of_isFinitary_piD (isFinitaryProjection_piD_of_formula d hii).out.2

end isFinitary

namespace isProjection

theorem piU (d : ApproximableMap U U) : IsProjection (DomainTheory.NeighbourhoodSystems.piU d) :=
  subU.isProjection_conjArrow (isProjection_piD d)

end isProjection

namespace isFinitaryProjection

theorem piU (d : ApproximableMap U U) : FinitaryProjection (DomainTheory.NeighbourhoodSystems.piU d) :=
  ⟨⟨isProjection.piU d, isFinitary.piU_of_isFinitary_piD (isFinitaryProjection_piD d).out.2⟩⟩

end isFinitaryProjection

end DomainTheory.NeighbourhoodSystems
