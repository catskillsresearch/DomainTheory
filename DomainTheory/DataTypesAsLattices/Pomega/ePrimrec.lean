module

public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Data.Nat.Find
public import DomainTheory.DataTypesAsLattices.Pomega.ePrimrecScan

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem primrecRel_mem_e : PrimrecRel fun n k => k ∈ e n := by
  refine Primrec₂.primrecRel (primrec_testBit.of_eq fun n k => ?_)
  simp [e.mem]

def eMax (n : ℕ) : ℕ := Nat.findGreatest (fun k => n.testBit k = true) n

theorem primrec_eMax : Primrec eMax := by
  have hrel : PrimrecRel fun (n k : ℕ) => Nat.testBit n k = true :=
    Primrec₂.primrecRel
      (primrec_testBit.of_eq fun n k => by
        cases h : n.testBit k <;> rfl)
  exact (Primrec.nat_findGreatest Primrec.id hrel).of_eq fun _ => rfl

theorem primrecRel_e_subset : PrimrecRel fun n m => e n ⊆ e m := by
  refine Primrec₂.primrecRel (primrec₂_eSubsetBool.of_eq fun n m => ?_)
  have hiff : e n ⊆ e m ↔ eSubsetBool n m = true := by
    simp only [Set.subset_def, e.mem, eSubsetBool_iff]
  cases hb : eSubsetBool n m <;> simp [hiff, hb]

theorem primrecPred_e_eq_union :
    PrimrecPred fun t : ℕ × ℕ × ℕ => e t.1 = e t.2.1 ∪ e t.2.2 := by
  refine Primrec.primrecPred (primrec_eEqUnionBool.of_eq fun t => ?_)
  cases hb : eEqUnionBool t.1 t.2.1 t.2.2 with
  | false =>
    have hnot : ¬ e t.1 = e t.2.1 ∪ e t.2.2 := by
      intro h
      have := (eEqUnionBool_iff t.1 t.2.1 t.2.2).mpr h
      simp [hb] at this
    simp [hnot]
  | true =>
    have hyes : e t.1 = e t.2.1 ∪ e t.2.2 :=
      (eEqUnionBool_iff t.1 t.2.1 t.2.2).mp (by simp [hb])
    simp [hyes]

/-- Scott (1976), §1: membership, inclusion, union-equality for `e`, and `eMax`. -/
theorem scott_e_primrec_structure :
    PrimrecRel (fun n k => k ∈ e n) ∧
      Primrec eMax ∧
        PrimrecRel (fun n m => e n ⊆ e m) ∧
          PrimrecPred (fun t : ℕ × ℕ × ℕ => e t.1 = e t.2.1 ∪ e t.2.2) :=
  ⟨primrecRel_mem_e, primrec_eMax, primrecRel_e_subset, primrecPred_e_eq_union⟩

end DomainTheory.DataTypesAsLattices
