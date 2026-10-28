module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.IsGraph
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.fixedToInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimitToFixed
public import DomainTheory.DataTypesAsLattices.Retracts.iterates_areRetracts
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_iUnion
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.iUnion_retract_isGraph
public import DomainTheory.DataTypesAsLattices.Retracts.funOf_fix_idem
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_4_6 {F : Pomega → Pomega}
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

namespace theorem_4_6

def inverseLimit {F : Pomega → Pomega}
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

theorem limit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    (∀ n, Retract (iterateBot F n)) ∧
      Retract (funOf Ycomb (graph F)) ∧
        ∃ φ : Fixpoints (funOf (fix F)) → RetractInverseLimit F,
          Function.Bijective φ ∧
            ∀ x y : Fixpoints (funOf (fix F)),
              (x : Pomega) ⊆ (y : Pomega) ↔
                ∀ n, (φ x).1 n ⊆ (φ y).1 n := by
  refine ⟨(theorem_4_6 hf hret).1, (theorem_4_6 hf hret).2, ?_⟩
  let iso := theorem_4_6.inverseLimit hf hret hstrict hmono
  refine ⟨iso, iso.bijective, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy n
    exact funOf.monotone_right (iterateBot F n) hxy
  · intro h
    have hx : (x : Pomega) = ⋃ n, funOf (iterateBot F n) (x : Pomega) := by
      calc
        (x : Pomega) = funOf (fix F) (x : Pomega) := x.property.symm
        _ = ⋃ n, funOf (iterateBot F n) (x : Pomega) := by
          change funOf (⋃ n, iterateBot F n) (x : Pomega) = _
          rw [funOf.iUnion]
    have hy : (y : Pomega) = ⋃ n, funOf (iterateBot F n) (y : Pomega) := by
      calc
        (y : Pomega) = funOf (fix F) (y : Pomega) := y.property.symm
        _ = ⋃ n, funOf (iterateBot F n) (y : Pomega) := by
          change funOf (⋃ n, iterateBot F n) (y : Pomega) = _
          rw [funOf.iUnion]
    change ∀ n, funOf (iterateBot F n) (x : Pomega) ⊆
      funOf (iterateBot F n) (y : Pomega) at h
    rw [hx, hy]
    intro k hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, h n hn⟩

end theorem_4_6

end DomainTheory.DataTypesAsLattices
