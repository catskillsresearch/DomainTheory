module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.piU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/- concordance: source L5267 EXERCISE 8.27 infinite cartesian products — tip packing -/

set_option linter.unusedVariables false

/-- Pack of the Exercise 8.27 library facts used by the tip (`exercise_8_27`). -/
theorem example_827 :
    (∀ (d : ApproximableMap U U) (x : (funSpace U U).Element) {Y₀ Z₀ : Set ℚ},
        piDApply d (toApproxMap x) ∈ step Y₀ Z₀ →
          ∃ X, x.mem X ∧ X ⊆ (step Y₀ Z₀ : Set (ApproximableMap U U)) ∧ (piD d).rel X X) ∧
    (∀ (d : ApproximableMap U U) {X W : Set (ApproximableMap U U)},
        (piD d).rel X W ↔
          ∃ hX : (funSpace U U).mem X, (funSpace U U).mem W ∧ gSection (piDUncurried d) hX ∈ W) ∧
    (∀ (d : ApproximableMap U U) {X : Set (ApproximableMap U U)} (hX : (funSpace U U).mem X)
        {Y Z : Set ℚ} (hY : U.mem Y),
        (gSection (piDUncurried d) hX).rel Y Z ↔
          ((piDApply d (toApproxMap ((funSpace U U).principal hX))).toElementMap
            (U.principal hY)).mem Z) ∧
    (∀ (d : ApproximableMap U U) (x : (funSpace U U).Element) {Y : Set (ApproximableMap U U)},
        ((piD d).toElementMap x).mem Y ↔
          (funSpace U U).mem Y ∧ piDApply d (toApproxMap x) ∈ Y) ∧
    (∀ (d : ApproximableMap U U) (x : (funSpace U U).Element) {Y : Set (ApproximableMap U U)}
        (hYE : (funSpace U U).mem Y) {X : Set (ApproximableMap U U)}
        (hXx : x.mem X) (hXY : X ⊆ Y) (hXX : (piD d).rel X X),
        ((piD d).toElementMap x).mem Y) ∧
    (∀ (d : ApproximableMap U U) (x : (funSpace U U).Element) (L : List (Set ℚ × Set ℚ)),
        piDApply d (toApproxMap x) ∈ stepFun L →
          ∃ X, x.mem X ∧ X ⊆ (stepFun L : Set (ApproximableMap U U)) ∧ (piD d).rel X X) ∧
    (∀ (d : ApproximableMap U U) (x : (funSpace U U).Element) {Y : Set (ApproximableMap U U)}
        (hYE : (funSpace U U).mem Y) (hmem : piDApply d (toApproxMap x) ∈ Y),
        ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) ∧
    (∀ (d : ApproximableMap U U) (x : (funSpace U U).Element) {Y : Set (ApproximableMap U U)},
        ((piD d).toElementMap x).mem Y ↔
          (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) ∧
    (∀ d : ApproximableMap U U, FinitaryProjection (piD d)) ∧
    (∀ (d : ApproximableMap U U),
        (∀ (x : (funSpace U U).Element) {Y}, ((piD d).toElementMap x).mem Y ↔
          (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) →
        FinitaryProjection (piD d)) ∧
    (∀ d : ApproximableMap U U, FinitaryProjection (piU d)) ∧
    (∀ {d : ApproximableMap U U},
        (∀ (x : (funSpace U U).Element) {Y}, ((piD d).toElementMap x).mem Y ↔
          (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) →
        IsFinitary (piU d)) ∧
    (∀ {d : ApproximableMap U U}, IsFinitary (piD d) → IsFinitary (piU d)) ∧
    (∀ (d : ApproximableMap U U) {X : Set (ApproximableMap U U)},
        (piD d).rel X X ↔ ∃ hX : (funSpace U U).mem X, gSection (piDUncurried d) hX ∈ X) :=
  ⟨exists_X_of_mem_step, piD_rel_iff, gSection_piDUncurried_rel_iff, piD_toElementMap_mem_iff,
    hii_easy_direction, exists_X_of_mem_stepFun, hii_hard_direction, hii_piD,
    isFinitaryProjection_piD, isFinitaryProjection_piD_of_formula, isFinitaryProjection.piU,
    isFinitary.piU_of_formula, isFinitary.piU_of_isFinitary_piD, piD_rel_self_iff⟩

end DomainTheory.NeighbourhoodSystems
