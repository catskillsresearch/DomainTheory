module

public import Mathlib.Computability.Primrec.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem primrec_twoPow : Primrec fun k : ℕ => 2 ^ k :=
  (Primrec.nat_rec' (f := id) (g := fun _ => (1 : ℕ))
    (h := fun (_ : ℕ) (p : ℕ × ℕ) => p.2 * 2)
    Primrec.id (Primrec.const 1)
    (show Primrec fun q : ℕ × ℕ × ℕ => q.2.2 * 2 from
      Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2))).of_eq
    fun k => by
      induction k with
      | zero => simp
      | succ k ih =>
        change (Nat.rec 1 (fun n IH => (n, IH).2 * 2) k) * 2 = 2 ^ (k + 1)
        have ih' : Nat.rec 1 (fun n IH => (n, IH).2 * 2) k = 2 ^ k := by
          simpa [id] using ih
        rw [ih', Nat.pow_succ, Nat.mul_comm]

theorem primrec_testBit : Primrec₂ fun n k : ℕ => n.testBit k :=
  (Primrec.eq.decide.comp
    (Primrec.nat_mod.comp
      (Primrec.nat_div.comp Primrec.fst (primrec_twoPow.comp Primrec.snd))
      (Primrec.const 2))
    (Primrec.const 1)).of_eq fun _p =>
      Nat.testBit_eq_decide_div_mod_eq.symm

theorem not_testBit_of_ge {n k : ℕ} (h : n ≤ k) : n.testBit k = false := by
  cases ht : n.testBit k with
  | false => rfl
  | true => exact (Nat.not_le_of_gt (e.mem_lt (e.mem.mpr ht)) h).elim

end DomainTheory.DataTypesAsLattices
