module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_iUnion
public import DomainTheory.DataTypesAsLattices.Retracts.fixedToInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimitToFixed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 4.6, inverse-limit half.** The maps
`u ↦ (Fⁿ(⊥)(u))ₙ` and `(vₙ) ↦ ⋃ₙ vₙ` are inverse order isomorphisms. -/
def theorem_4_6_inverseLimit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    Fixpoints (funOf (fix F)) ≃o RetractInverseLimit F where
  toFun := fixedToInverseLimit hf hret hstrict hmono
  invFun := inverseLimitToFixed hf hret hstrict hmono
  left_inv u := by
    apply Subtype.ext
    change (⋃ n, funOf (iterateBot F n) u.1) = u.1
    rw [← funOf_iUnion, ← fix, u.property]
  right_inv v := by
    apply Subtype.ext
    funext n
    exact inverseLimit_project_iUnion hf hret hstrict hmono v n
  map_rel_iff' := by
    intro u w
    constructor
    · intro h
      change ∀ n, funOf (iterateBot F n) u.1 ⊆
        funOf (iterateBot F n) w.1 at h
      change u.1 ⊆ w.1
      have hu : u.1 = ⋃ n, funOf (iterateBot F n) u.1 := by
        calc
          u.1 = funOf (fix F) u.1 := u.property.symm
          _ = ⋃ n, funOf (iterateBot F n) u.1 := by
            change funOf (⋃ n, iterateBot F n) u.1 = _
            rw [funOf_iUnion]
      have hw : w.1 = ⋃ n, funOf (iterateBot F n) w.1 := by
        calc
          w.1 = funOf (fix F) w.1 := w.property.symm
          _ = ⋃ n, funOf (iterateBot F n) w.1 := by
            change funOf (⋃ n, iterateBot F n) w.1 = _
            rw [funOf_iUnion]
      rw [hu, hw]
      intro k hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨n, h n hkn⟩
    · intro huw
      change u.1 ⊆ w.1 at huw
      change ∀ n, funOf (iterateBot F n) u.1 ⊆
        funOf (iterateBot F n) w.1
      intro n
      exact funOf_monotone_right (iterateBot F n) huw

end DomainTheory.DataTypesAsLattices
