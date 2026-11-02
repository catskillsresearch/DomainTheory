module

public import Mathlib.Computability.Primrec.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e
import DomainTheory.DataTypesAsLattices.Pomega.eScan

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem primrecRel_mem_e : PrimrecRel fun n k => k ∈ e n :=
  primrecRel_testBit_true.of_eq fun n k => by simp [e.mem]

def eMax (n : ℕ) : ℕ := Nat.findGreatest (fun k => n.testBit k = true) n

theorem primrec_eMax : Primrec eMax := by
  exact (Primrec.nat_findGreatest Primrec.id primrecRel_testBit_true).of_eq fun _ => rfl

theorem primrecRel_e_subset : PrimrecRel fun n m => e n ⊆ e m :=
  (Primrec.eq.comp primrec_e_subsetBool (Primrec.const true)).of_eq fun p =>
    eSubsetBool_iff p.1 p.2

theorem primrecPred_e_eq_union :
    PrimrecPred fun t : ℕ × ℕ × ℕ => e t.1 = e t.2.1 ∪ e t.2.2 :=
  (Primrec.eq.comp primrec_e_eqUnionBool (Primrec.const true)).of_eq fun t =>
    eEqUnionBool_iff t.1 t.2.1 t.2.2

/-- Scott (1976), §1: membership, inclusion, union-equality for `e`, and `eMax`. -/
theorem scott_e_primrec_structure :
    PrimrecRel (fun n k => k ∈ e n) ∧
      Primrec eMax ∧
        PrimrecRel (fun n m => e n ⊆ e m) ∧
          PrimrecPred (fun t : ℕ × ℕ × ℕ => e t.1 = e t.2.1 ∪ e t.2.2) :=
  ⟨primrecRel_mem_e, primrec_eMax, primrecRel_e_subset, primrecPred_e_eq_union⟩

end DomainTheory.DataTypesAsLattices
