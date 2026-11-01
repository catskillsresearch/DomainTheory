module

public import DomainTheory.DataTypesAsLattices.Pomega.eDecidable
public import DomainTheory.DataTypesAsLattices.Pomega.ePrimrecBit

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def eSubsetBoolAux (n m fuel : ℕ) : Bool :=
  fuel.rec true fun k ih => ih && (!(n.testBit k) || m.testBit k)

def eSubsetBool (n m : ℕ) : Bool := eSubsetBoolAux n m n

theorem eSubsetBoolAux_succ (n m fuel : ℕ) :
    eSubsetBoolAux n m (fuel + 1) =
      (eSubsetBoolAux n m fuel && (!(n.testBit fuel) || m.testBit fuel)) :=
  rfl

theorem eSubsetBoolAux_iff (n m fuel : ℕ) :
    eSubsetBoolAux n m fuel = true ↔
      ∀ k < fuel, n.testBit k = true → m.testBit k = true := by
  induction fuel with
  | zero => simp [eSubsetBoolAux]
  | succ fuel ih =>
    rw [eSubsetBoolAux_succ]
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

theorem eSubsetBool_iff (n m : ℕ) :
    eSubsetBool n m = true ↔ ∀ k, n.testBit k = true → m.testBit k = true := by
  rw [eSubsetBool, eSubsetBoolAux_iff]
  constructor
  · intro h k hk
    by_cases hkn : k < n
    · exact h k hkn hk
    · exact absurd hk (by simp [not_testBit_of_ge (Nat.le_of_not_gt hkn)])
  · intro h k _ hk
    exact h k hk

theorem primrec₂_eSubsetBool : Primrec₂ eSubsetBool := by
  have hstep : Primrec₂ fun (p : ℕ × ℕ) (nih : ℕ × Bool) =>
      nih.2 && (!(p.1.testBit nih.1) || p.2.testBit nih.1) :=
    Primrec.and.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.or.comp
        (Primrec.not.comp
          (primrec_testBit.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
        (primrec_testBit.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
  exact (Primrec.nat_rec' Primrec.fst (Primrec.const true) hstep).of_eq fun _ => rfl

def eEqUnionBoolAux (n m k fuel : ℕ) : Bool :=
  fuel.rec true fun i ih => ih && (n.testBit i == (m.testBit i || k.testBit i))

def eEqUnionBool (n m k : ℕ) : Bool := eEqUnionBoolAux n m k (n + m + k + 1)

theorem eEqUnionBoolAux_succ (n m k fuel : ℕ) :
    eEqUnionBoolAux n m k (fuel + 1) =
      (eEqUnionBoolAux n m k fuel && (n.testBit fuel == (m.testBit fuel || k.testBit fuel))) :=
  rfl

theorem eEqUnionBoolAux_iff (n m k fuel : ℕ) :
    eEqUnionBoolAux n m k fuel = true ↔
      ∀ i < fuel, n.testBit i = (m.testBit i || k.testBit i) := by
  induction fuel with
  | zero => simp [eEqUnionBoolAux]
  | succ fuel ih =>
    rw [eEqUnionBoolAux_succ]
    simp only [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hb⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · exact h i hlt
      · simpa [beq_iff_eq] using hb
    · intro h
      refine ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), ?_⟩
      simpa [beq_iff_eq] using h fuel (Nat.lt_succ_self fuel)

theorem eEqUnionBool_iff (n m k : ℕ) :
    eEqUnionBool n m k = true ↔ e n = e m ∪ e k := by
  rw [eEqUnionBool, eEqUnionBoolAux_iff]
  constructor
  · intro h
    ext i
    simp only [Set.mem_union, e.mem]
    by_cases hi : i < n + m + k + 1
    · rw [h i hi]
      simp
    · have hle : n + m + k + 1 ≤ i := Nat.le_of_not_gt (by simpa [gt_iff_lt] using hi)
      have hn_le : n ≤ n + m + k + 1 := by
        simp [Nat.add_assoc]
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
      rw [← e.mem, ← e.mem, ← e.mem, h, Set.mem_union]
    cases hn : n.testBit i <;> cases hm : m.testBit i <;> cases hk : k.testBit i <;>
      simp [hn, hm, hk] at hmem ⊢

theorem primrec_eEqUnionBool : Primrec fun t : ℕ × ℕ × ℕ => eEqUnionBool t.1 t.2.1 t.2.2 := by
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

instance (n m k : ℕ) : Decidable (e n = e m ∪ e k) :=
  decidable_of_iff (eEqUnionBool n m k = true) (eEqUnionBool_iff n m k)

end DomainTheory.DataTypesAsLattices
