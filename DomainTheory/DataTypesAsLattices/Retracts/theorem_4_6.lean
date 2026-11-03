module

public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Retracts.fixedToInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimitToFixed
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
import DomainTheory.DataTypesAsLattices.Retracts.funOf_fix_idem
import DomainTheory.DataTypesAsLattices.Retracts.iUnion_retract_isGraph
import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_iUnion
import DomainTheory.DataTypesAsLattices.Retracts.iterates_areRetracts
import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace theorem_4_6

/-- Scott’s first sentence of Theorem 4.6: the iterates \(F^n(\bot)\) and
\(\mathbf{Y}(F)\) are retracts. -/
theorem Limit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a)) :
    (∀ n, Retract (iterateBot F n)) ∧
      Retract (funOf Ycomb (graph F)) := by
  refine ⟨iterates_areRetracts hret, ?_⟩
  have hY : funOf Ycomb (graph F) = fix F := theorem_2_5 hf
  rw [hY]
  constructor
  change fix F = graph (fun x => funOf (fix F) (funOf (fix F) x))
  have hG : IsGraph (fix F) :=
    iUnion_retract_isGraph (iterates_areRetracts hret)
  have hgr : graph (funOf (fix F)) = fix F := (theorem_1_2.iii (fix F)).mpr hG
  have hidem' : graph (fun x => funOf (fix F) (funOf (fix F) x)) =
      graph (funOf (fix F)) :=
    graph_ext (fun x => funOf_fix_idem hf hret x)
  exact (hidem'.trans hgr).symm

/-- Scott’s second sentence of Theorem 4.6: under strictness and monotonicity,
the range of \(\mathbf{Y}(F)\) is order-isomorphic to the inverse limit of the
ranges of \(F^n(\bot)\). -/
def InverseLimit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    Fixpoints (funOf (fix F)) ≃o RetractInverseLimit F where
  toFun := fixedToInverseLimit hf hret hstrict hmono
  invFun := inverseLimitToFixed hf hret hstrict hmono
  left_inv u := by
    apply Subtype.ext
    change (⋃ n, funOf (iterateBot F n) u.1) = u.1
    rw [← funOf.iUnion, ← fix, u.property]
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
            rw [funOf.iUnion]
      have hw : w.1 = ⋃ n, funOf (iterateBot F n) w.1 := by
        calc
          w.1 = funOf (fix F) w.1 := w.property.symm
          _ = ⋃ n, funOf (iterateBot F n) w.1 := by
            change funOf (⋃ n, iterateBot F n) w.1 = _
            rw [funOf.iUnion]
      rw [hu, hw]
      intro k hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨n, h n hkn⟩
    · intro huw
      change u.1 ⊆ w.1 at huw
      change ∀ n, funOf (iterateBot F n) u.1 ⊆
        funOf (iterateBot F n) w.1
      intro n
      exact funOf.monotone_right (iterateBot F n) huw

/-- Scott’s second sentence as a proposition: the ranges are order-isomorphic
(witnessed by `InverseLimit`). -/
theorem inverse_limit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    Nonempty (Fixpoints (funOf (fix F)) ≃o RetractInverseLimit F) :=
  ⟨InverseLimit hf hret hstrict hmono⟩

end theorem_4_6

/-- Scott’s Theorem 4.6: the two sentences, as two theorems. -/
theorem theorem_4_6 {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    ((∀ n, Retract (iterateBot F n)) ∧
      Retract (funOf Ycomb (graph F))) ∧
      Nonempty (Fixpoints (funOf (fix F)) ≃o RetractInverseLimit F) :=
  ⟨theorem_4_6.Limit hf hret, theorem_4_6.inverse_limit hf hret hstrict hmono⟩

end DomainTheory.DataTypesAsLattices
