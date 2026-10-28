module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

noncomputable def yFoldStep (w : ℕ) : ℕ :=
  let n := w.unpair.1
  let i := w.unpair.2.unpair.1
  let acc := w.unpair.2.unpair.2
  let k := i + 2 ^ n
  selectFn (atomUEmpty P (n + 1) k) acc
    (selectFn acc.unpair.1
      (Nat.pair 1 (unionUX acc.unpair.2 (atomUCode P (n + 1) k)))
      (Nat.pair 1 (atomUCode P (n + 1) k)))

noncomputable def yFold (n N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => yFoldStep P (Nat.pair n (Nat.pair i acc)))

noncomputable def YseqCode (n : ℕ) : ℕ := (yFold P n (2 ^ n)).unpair.2

def Yc (m : ℕ) : Set ℚ := UX (YseqCode P m)

theorem yFoldStep_eq (n i acc : ℕ) :
    yFoldStep P (Nat.pair n (Nat.pair i acc)) =
      selectFn (atomUEmpty P (n + 1) (i + 2 ^ n)) acc
        (selectFn acc.unpair.1
          (Nat.pair 1 (unionUX acc.unpair.2 (atomUCode P (n + 1) (i + 2 ^ n))))
          (Nat.pair 1 (atomUCode P (n + 1) (i + 2 ^ n)))) := by
  unfold yFoldStep
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem yFold_succ (n N : ℕ) :
    yFold P n (N + 1) = yFoldStep P (Nat.pair n (Nat.pair N (yFold P n N))) := rfl

theorem yFold_zero (n : ℕ) : yFold P n 0 = Nat.pair 0 0 := rfl

theorem yFold_found_le_one (n : ℕ) : ∀ N, (yFold P n N).unpair.1 ≤ 1 := by
  intro N
  induction N with
  | zero => simp [yFold_zero]
  | succ N ih =>
    rw [yFold_succ, yFoldStep_eq]
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero]
      rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf0 | hfpos
      · rw [show (yFold P n N).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_fst]
      · rw [show (yFold P n N).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
    · rw [h1, selectFn_one]; exact ih

theorem yFold_found_iff (n : ℕ) :
    ∀ N, (yFold P n N).unpair.1 = 1 ↔ ∃ i < N, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 := by
  intro N
  induction N with
  | zero => simp [yFold_zero]
  | succ N ih =>
    rw [yFold_succ, yFoldStep_eq]
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero]
      have hval1 : (selectFn (yFold P n N).unpair.1
          (Nat.pair 1 (unionUX (yFold P n N).unpair.2 (atomUCode P (n + 1) (N + 2 ^ n))))
          (Nat.pair 1 (atomUCode P (n + 1) (N + 2 ^ n)))).unpair.1 = 1 := by
        have hle := yFold_found_le_one P n N
        rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf | hf
        · rw [show (yFold P n N).unpair.1 = 0 from hf, selectFn_zero, unpair_pair_fst]
        · rw [show (yFold P n N).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
      rw [hval1]
      exact ⟨fun _ => ⟨N, Nat.lt_succ_self N, h0⟩, fun _ => rfl⟩
    · rw [h1, selectFn_one, ih]
      constructor
      · rintro ⟨i, hi, hie⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie⟩
      · rintro ⟨i, hi, hie⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie⟩
        · exact absurd hie (by omega)

end DomainTheory.NeighbourhoodSystems
