module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.FixedPoint.chain_lemma
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_mono
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_chain
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_later
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_earlier
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Every stage projection of the union of a coherent sequence is its
corresponding coordinate. -/
theorem inverseLimit_project_iUnion {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) (n : ℕ) :
    funOf (iterateBot F n) (⋃ m, v.1 m) = v.1 n := by
  rw [chain_lemma (funOf.isScottContinuous (iterateBot F n)) v.1
    (inverseLimit_mono hf v)]
  apply subset_antisymm
  · intro k hk
    obtain ⟨m, hkm⟩ := Set.mem_iUnion.mp hk
    by_cases hmn : m ≤ n
    · rw [inverseLimit_project_earlier hret hstrict hmono v hmn] at hkm
      exact inverseLimit_chain hf v m n hmn hkm
    · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      rwa [inverseLimit_project_later hret hstrict hmono v hnm] at hkm
  · intro k hk
    exact Set.mem_iUnion.mpr ⟨n, by
      rw [inverseLimit_project_later hret hstrict hmono v (le_refl n)]
      exact hk⟩

end DomainTheory.DataTypesAsLattices
