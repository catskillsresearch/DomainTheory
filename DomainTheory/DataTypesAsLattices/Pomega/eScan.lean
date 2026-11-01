module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

set_option maxHeartbeats 2000000

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

theorem primrecRel_testBit_true : PrimrecRel fun (n k : ℕ) => n.testBit k = true :=
  Primrec.eq.comp primrec_testBit (Primrec.const true)

namespace e

private abbrev Enc := _root_.DomainTheory.DataTypesAsLattices.e

private theorem mem_iff {n k : ℕ} : k ∈ Enc n ↔ n.testBit k := by
  rw [Enc, mem]

private def subsetBoolAux (n m fuel : ℕ) : Bool :=
  fuel.rec true fun k ih => ih && (!(n.testBit k) || m.testBit k)

def subsetBool (n m : ℕ) : Bool := subsetBoolAux n m n

private theorem subsetBoolAux_succ (n m fuel : ℕ) :
    subsetBoolAux n m (fuel + 1) =
      (subsetBoolAux n m fuel && (!(n.testBit fuel) || m.testBit fuel)) :=
  rfl

private theorem subsetBoolAux_iff (n m fuel : ℕ) :
    subsetBoolAux n m fuel = true ↔
      ∀ k < fuel, n.testBit k = true → m.testBit k = true := by
  induction fuel with
  | zero => simp [subsetBoolAux]
  | succ fuel ih =>
    rw [subsetBoolAux_succ]
    simp only [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hb⟩ k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
      · exact h k hlt
      · intro hk'
        simp [hk'] at hb
        exact hb
    · intro h
      refine ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), ?_⟩
      by_cases hk : n.testBit fuel = true
      · simp [h fuel (Nat.lt_succ_self fuel) hk]
      · simp [hk]

theorem subsetBool_iff (n m : ℕ) :
    subsetBool n m = true ↔ ∀ k, n.testBit k = true → m.testBit k = true := by
  rw [subsetBool, subsetBoolAux_iff]
  constructor
  · intro h k hk
    by_cases hkn : k < n
    · exact h k hkn hk
    · exact absurd hk (by simp [not_testBit_of_ge (Nat.le_of_not_gt hkn)])
  · intro h k _ hk
    exact h k hk

private def eqUnionBoolAux (n m k fuel : ℕ) : Bool :=
  fuel.rec true fun i ih => ih && (n.testBit i == (m.testBit i || k.testBit i))

def eqUnionBool (n m k : ℕ) : Bool := eqUnionBoolAux n m k (n + m + k + 1)

private theorem eqUnionBoolAux_succ (n m k fuel : ℕ) :
    eqUnionBoolAux n m k (fuel + 1) =
      (eqUnionBoolAux n m k fuel && (n.testBit fuel == (m.testBit fuel || k.testBit fuel))) :=
  rfl

private theorem eqUnionBoolAux_iff (n m k fuel : ℕ) :
    eqUnionBoolAux n m k fuel = true ↔
      ∀ i < fuel, n.testBit i = (m.testBit i || k.testBit i) := by
  induction fuel with
  | zero => simp [eqUnionBoolAux]
  | succ fuel ih =>
    rw [eqUnionBoolAux_succ]
    simp only [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hb⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · exact h i hlt
      · simpa [beq_iff_eq] using hb
    · intro h
      refine ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), ?_⟩
      simpa [beq_iff_eq] using h fuel (Nat.lt_succ_self fuel)

theorem eqUnionBool_iff (n m k : ℕ) :
    eqUnionBool n m k = true ↔ Enc n = Enc m ∪ Enc k := by
  rw [eqUnionBool, eqUnionBoolAux_iff]
  constructor
  · intro h
    ext i
    rw [mem_iff, Set.mem_union, mem_iff (n := m), mem_iff (n := k)]
    by_cases hi : i < n + m + k + 1
    · rw [h i hi]
      simp
    · have hle : n + m + k + 1 ≤ i := Nat.le_of_not_gt (by simpa [gt_iff_lt] using hi)
      have hn_le : n ≤ n + m + k + 1 := by simp [Nat.add_assoc]
      have hm_le : m ≤ n + m + k + 1 :=
        Nat.le_trans (Nat.le_add_left m n) (Nat.le_add_right (n + m) (k + 1))
      have hk_le : k ≤ n + m + k + 1 := by
        calc
          k ≤ n + m + 1 + k := Nat.le_add_left k (n + m + 1)
          _ = n + m + k + 1 := by
            rw [Nat.add_assoc (n + m) 1 k, Nat.add_comm 1 k, ← Nat.add_assoc (n + m) k 1]
      have hn := not_testBit_of_ge (Nat.le_trans hn_le hle)
      have hm := not_testBit_of_ge (Nat.le_trans hm_le hle)
      have hk := not_testBit_of_ge (Nat.le_trans hk_le hle)
      simp [hn, hm, hk]
  · intro h i _
    have hmem : n.testBit i = true ↔ m.testBit i = true ∨ k.testBit i = true := by
      rw [← mem_iff, h, Set.mem_union, ← mem_iff (n := m), ← mem_iff (n := k)]
    cases hn : n.testBit i <;> cases hm : m.testBit i <;> cases hk : k.testBit i <;>
      simp [hn, hm, hk] at hmem ⊢

end e

theorem eSubsetBool_iff (n m : ℕ) :
    e.subsetBool n m = true ↔ e n ⊆ e m := by
  simp [Set.subset_def, e.mem, e.subsetBool_iff]

theorem eEqUnionBool_iff (n m k : ℕ) :
    e.eqUnionBool n m k = true ↔ e n = e m ∪ e k :=
  e.eqUnionBool_iff n m k

theorem primrec_e_subsetBool : Primrec₂ e.subsetBool := by
  have hstep : Primrec₂ fun (p : ℕ × ℕ) (nih : ℕ × Bool) =>
      nih.2 && (!(p.1.testBit nih.1) || p.2.testBit nih.1) :=
    Primrec.and.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.or.comp
        (Primrec.not.comp
          (primrec_testBit.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
        (primrec_testBit.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
  exact (Primrec.nat_rec' Primrec.fst (Primrec.const true) hstep).of_eq fun _ => rfl

theorem primrec_e_eqUnionBool : Primrec fun t : ℕ × ℕ × ℕ =>
    e.eqUnionBool t.1 t.2.1 t.2.2 := by
  have hbound : Primrec fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 + 1 :=
    Primrec.succ.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ fun (p : ℕ × ℕ × ℕ) (nih : ℕ × Bool) =>
      nih.2 && (p.1.testBit nih.1 == (p.2.1.testBit nih.1 || p.2.2.testBit nih.1)) :=
    Primrec.and.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.beq.comp
        (primrec_testBit.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.or.comp
          (primrec_testBit.comp
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))
          (primrec_testBit.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))))
  exact (Primrec.nat_rec' hbound (Primrec.const true) hstep).of_eq fun _ => rfl

end DomainTheory.DataTypesAsLattices
