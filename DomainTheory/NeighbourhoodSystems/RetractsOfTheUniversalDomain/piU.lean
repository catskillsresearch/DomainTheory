module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.PolymorphicType

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **`Π(d)`, regarded as a combinator living in `𝒰` itself** — conjugating `piD d` through
`i_→, j_→` (Definition 8.9), exactly as `subU` was built from `subApprox` in Step 1. This is what
Scott's "type" means: a self-map *of `𝒰`*, not of `(𝒰→𝒰)`. -/
noncomputable def piU (d : ApproximableMap U U) : ApproximableMap U U :=
  iArrow.comp ((piD d).comp jArrow)

namespace toElementMap

/-- `piU d`'s defining formula unfolded at the element level (mirrors `toElementMap_subU`). -/
theorem piU (d : ApproximableMap U U) (w : U.Element) :
    (DomainTheory.NeighbourhoodSystems.piU d).toElementMap w =
      iArrow.toElementMap ((piD d).toElementMap (jArrow.toElementMap w)) := by
  unfold DomainTheory.NeighbourhoodSystems.piU
  rw [toElementMap_comp, toElementMap_comp]

end toElementMap

namespace piD

/-- Unfolds `(piU d).toElementMap w = w` into the statement that `j_→(w)` is already a fixed
point of `piD d` (mirrors `subApprox_fix_of_subU_fix`). -/
theorem fix_of_piU_fix {d : ApproximableMap U U} {w : U.Element}
    (hw : (piU d).toElementMap w = w) :
    (piD d).toElementMap (jArrow.toElementMap w) = jArrow.toElementMap w := by
  rw [toElementMap.piU] at hw
  have hstep := congrArg jArrow.toElementMap hw
  rwa [jArrow_comp_iArrow_apply] at hstep

end piD

namespace piU

/-- Mirrors `subU_fix_of_subApprox_fix`. -/
theorem fix_of_piD_fix {d : ApproximableMap U U} {φ : (funSpace U U).Element}
    (hφ : (piD d).toElementMap φ = φ) :
    (piU d).toElementMap (iArrow.toElementMap φ) = iArrow.toElementMap φ := by
  rw [toElementMap.piU, jArrow_comp_iArrow_apply, hφ]

/-- **Exercise 8.27(b)(0): `Fix(piU d) ≃o Fix(piD d)`.** Forward: `w ↦ j_→(w)`; backward:
`φ ↦ i_→(φ)`. Needs only `j_→∘i_→ = I` (no inequality on `i_→∘j_→`) — mirrors `subUFixIso`
verbatim, with `piD d`/`piU d` in place of `subApprox`/`subU`. -/
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

/-- **Exercise 8.27(b)(0), corollary: if `piD d` is finitary then so is `piU d`.** Mirrors
`isFinitary_subU`'s use of `subUFixIso`. This is the reduction Exercise 8.27(b)(1)–(b)(4) will
target: it suffices to prove `IsFinitary (piD d)` for `d` polymorphic. -/
theorem piU_of_isFinitary_piD {d : ApproximableMap U U} (h : IsFinitary (piD d)) :
    IsFinitary (piU d) := by
  obtain ⟨β, F, ⟨iso⟩⟩ := h
  exact ⟨β, F, ⟨(piU.FixIso d).trans iso⟩⟩

/-- **Exercise 8.27(b)(1), assembled with (b)(0):** formula (ii) for `piD d` alone gives
`IsFinitary (piU d)`, i.e. (combined with the already-Pass 8.27(a)) the *entire* exercise for `d`
polymorphic. This pins down exactly what Exercise 8.27(b)(2)–(b)(3) need to supply: `hii`. -/
theorem piU_of_formula {d : ApproximableMap U U}
    (hii : ∀ (x : (funSpace U U).Element) {Y}, ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) :
    IsFinitary (piU d) :=
  piU_of_isFinitary_piD (isFinitaryProjection_piD_of_formula d hii).out.2

end isFinitary

namespace isProjection

/-- **`Π(d)`, regarded as living in `𝒰` (`piU d`), is a projection, for every `d`.** Half of "for
`d` a polymorphic type, `Π(d)` is a type" (Definition 8.3's `IsProjection` clause) — Scott's own
"it is easy to check" — obtained "for free" from `isProjection_piD` via the same conjugation
gadget (`isProjection_conjArrow`) used for `subU` in Step 1. Note this does not even need `d` to
be a polymorphic type. -/
theorem piU (d : ApproximableMap U U) : IsProjection (DomainTheory.NeighbourhoodSystems.piU d) :=
  isProjection_conjArrow (isProjection_piD d)

end isProjection

namespace isFinitaryProjection

/-- **Exercise 8.27, in full: for `d` a polymorphic type, `Π(d)` is a type.** (In fact for *any*
`d` at all — see `isFinitaryProjection_piD`.) This is the exercise's own statement, the last exercise
in the book, closed. -/
theorem piU (d : ApproximableMap U U) : FinitaryProjection (DomainTheory.NeighbourhoodSystems.piU d) :=
  ⟨⟨isProjection.piU d, isFinitary.piU_of_isFinitary_piD (isFinitaryProjection_piD d).out.2⟩⟩

end isFinitaryProjection

end DomainTheory.NeighbourhoodSystems
