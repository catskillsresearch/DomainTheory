module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.subApprox
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

theorem jArrow_comp_iArrow_apply (v : (funSpace U U).Element) :
    jArrow.toElementMap (iArrow.toElementMap v) = v := by
  rw [show jArrow.toElementMap (iArrow.toElementMap v) = (jArrow.comp iArrow).toElementMap v from
    (toElementMap_comp jArrow iArrow v).symm, jArrow_comp_iArrow, toElementMap_idMap]

noncomputable def subU : ApproximableMap U U :=
  iArrow.comp (subApprox.comp jArrow)

namespace subU

theorem toElementMap_eq (w : U.Element) :
    ApproximableMap.toElementMap subU w =
      iArrow.toElementMap (ApproximableMap.toElementMap subApprox (jArrow.toElementMap w)) := by
  unfold subU
  rw [toElementMap_comp, toElementMap_comp]

theorem subApprox_fix_of_fix {w : U.Element}
    (hw : ApproximableMap.toElementMap subU w = w) :
    ApproximableMap.toElementMap subApprox (jArrow.toElementMap w) = jArrow.toElementMap w := by
  rw [toElementMap_eq] at hw
  have hstep := congrArg jArrow.toElementMap hw
  rwa [jArrow_comp_iArrow_apply] at hstep

theorem fix_of_subApprox_fix {φ : (funSpace U U).Element}
    (hφ : ApproximableMap.toElementMap subApprox φ = φ) :
    ApproximableMap.toElementMap subU (iArrow.toElementMap φ) = iArrow.toElementMap φ := by
  rw [toElementMap_eq, jArrow_comp_iArrow_apply, hφ]

noncomputable def fixIso :
    {w : U.Element // ApproximableMap.toElementMap subU w = w} ≃o
      {φ : (funSpace U U).Element // ApproximableMap.toElementMap subApprox φ = φ} where
  toFun w := ⟨jArrow.toElementMap w.1, subApprox_fix_of_fix w.2⟩
  invFun φ := ⟨iArrow.toElementMap φ.1, fix_of_subApprox_fix φ.2⟩
  left_inv w := by
    apply Subtype.ext
    show iArrow.toElementMap (jArrow.toElementMap w.1) = w.1
    have hw := toElementMap_eq w.1
    rw [w.2] at hw
    rw [subApprox_fix_of_fix w.2] at hw
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
        have hw := toElementMap_eq w.1
        rw [w.2, subApprox_fix_of_fix w.2] at hw
        exact hw.symm
      have e2 : iArrow.toElementMap (jArrow.toElementMap w'.1) = w'.1 := by
        have hw' := toElementMap_eq w'.1
        rw [w'.2, subApprox_fix_of_fix w'.2] at hw'
        exact hw'.symm
      rwa [e1, e2] at h2
    · intro hle
      exact jArrow.toElementMap_mono hle

noncomputable def fixIsoSubFixed :
    {w : U.Element // ApproximableMap.toElementMap subU w = w} ≃o
      {f : ApproximableMap U U // sub f = f} :=
  fixIso.trans subApprox.fixIso

theorem isRetraction_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : Retraction H) : Retraction (iArrow.comp (H.comp jArrow)) := by
  constructor
  show (iArrow.comp (H.comp jArrow)).comp (iArrow.comp (H.comp jArrow)) =
    iArrow.comp (H.comp jArrow)
  rw [comp_assoc iArrow (H.comp jArrow) (iArrow.comp (H.comp jArrow)),
    comp_assoc H jArrow (iArrow.comp (H.comp jArrow)),
    ← comp_assoc jArrow iArrow (H.comp jArrow), jArrow_comp_iArrow, idMap_comp,
    ← comp_assoc H H jArrow, hH.out]

theorem le_idMap_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : H ≤ idMap (funSpace U U)) : iArrow.comp (H.comp jArrow) ≤ idMap U :=
  calc iArrow.comp (H.comp jArrow)
      ≤ iArrow.comp ((idMap (funSpace U U)).comp jArrow) :=
        comp_mono_gen le_rfl (comp_mono_gen hH le_rfl)
    _ = iArrow.comp jArrow := by rw [idMap_comp]
    _ ≤ idMap U := iArrow_comp_jArrow_le

theorem isProjection_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : IsProjection H) : IsProjection (iArrow.comp (H.comp jArrow)) :=
  ⟨isRetraction_conjArrow hH.1, le_idMap_conjArrow hH.2⟩

theorem isProjection : IsProjection subU :=
  isProjection_conjArrow Sub8_6.isProjection_subApprox

theorem isFinitary : IsFinitary subU := by
  obtain ⟨β, F, ⟨iso⟩⟩ := subApprox.isFinitary (E := U)
  exact ⟨β, F, ⟨fixIso.trans iso⟩⟩

theorem isFinitaryProjection : FinitaryProjection subU :=
  ⟨⟨isProjection, isFinitary⟩⟩

end subU

end DomainTheory.NeighbourhoodSystems
