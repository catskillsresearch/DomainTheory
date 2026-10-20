/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise717
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Proposition77
import DomainTheory.Neighborhood.Exercise717Part2.Basic
import DomainTheory.Neighborhood.Exercise717Part2.pair_lt_pair_of_lt_le
import DomainTheory.Neighborhood.Exercise717Part2.gStep_gamma
import DomainTheory.Neighborhood.Exercise717Part2.gStep_leaf
import DomainTheory.Neighborhood.Exercise717Part2.gStep_node
import DomainTheory.Neighborhood.Exercise717Part2.gEval_pair
import DomainTheory.Neighborhood.Exercise717Part2.listGet_rtbl_gEval
import DomainTheory.Neighborhood.Exercise717Part2.gEval_out


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

















section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)



set_option maxHeartbeats 1000000 in
/-- **Completeness of the certificate.** If `g` relates `V_n` to some `Z`, there is a `cert` the memo
certifies (ok-bit `1`) with `Q_{out} = Z`. Strong induction on `n`; the node case builds the certificate
from the children's certificates (children codes are `<` by `pair_lt_pair_of_lt_le`). -/
theorem gEval_complete (hD : ∀ X, D.mem X → X.Nonempty)
    (P : ComputablePresentation D) (Q : ComputablePresentation E)
    (hEq : ∀ m, fe (Nat.pair m mIdx) = 1 ↔ Q.X m = E.master) (hMidx : Q.X mIdx = E.master)
    (hU : ∀ a m, (∃ i, fU (Nat.pair i (Nat.pair a m)) = 1) ↔ u.rel (P.X a) (Q.X m))
    (hV : ∀ k1 k2 m, (∃ i, fV (Nat.pair i (Nat.pair (Nat.pair k1 k2) m)) = 1) ↔
        v.rel (prodNbhd (Q.X k1) (Q.X k2)) (Q.X m)) :
    ∀ n Z, GRel u v (Vsharp D P n) Z →
      ∃ cert, (gEval fe fU fV mIdx (Nat.pair n cert)).unpair.1 = 1
        ∧ Q.X cert.unpair.1 = Z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z hg
    rcases nat_shape n with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · -- n = 0
      rw [Vsharp_zero] at hg
      have hZ := gRel_gamma_inv hD hg
      refine ⟨Nat.pair mIdx (Nat.pair 0 0), ?_, ?_⟩
      · rw [gEval_pair, gStep_gamma, unpair_pair_fst, unpair_pair_fst]
        exact (hEq mIdx).mpr hMidx
      · rw [unpair_pair_fst, hMidx, hZ]
    · -- n = 2a+1
      rw [Vsharp_odd] at hg
      have hu := gRel_embZero_inv hD hg
      obtain ⟨e, he⟩ := Q.surj (u.rel_cod hu)
      rw [← he] at hu
      obtain ⟨wit, hwit⟩ := (hU a e).mpr hu
      refine ⟨Nat.pair e (Nat.pair wit 0), ?_, ?_⟩
      · rw [gEval_pair, gStep_leaf, unpair_pair_fst, unpair_pair_snd, unpair_pair_fst,
          unpair_pair_fst]
        exact hwit
      · rw [unpair_pair_fst]; exact he
    · -- n = 2a+2
      rw [Vsharp_even] at hg
      obtain ⟨Z₁, Z₂, hg1, hg2, hvrel⟩ := gRel_embPair_inv hD hg
      obtain ⟨certL, hokL, heqL⟩ := ih a.unpair.1 (by have := unpair_fst_le a; omega) Z₁ hg1
      obtain ⟨certR, hokR, heqR⟩ := ih a.unpair.2 (by have := unpair_snd_le a; omega) Z₂ hg2
      obtain ⟨e, he⟩ := Q.surj (v.rel_cod hvrel)
      rw [← heqL, ← heqR, ← he] at hvrel
      obtain ⟨wit, hwit⟩ := (hV certL.unpair.1 certR.unpair.1 e).mpr hvrel
      refine ⟨Nat.pair e (Nat.pair wit (Nat.pair certL certR)), ?_, ?_⟩
      · rw [gEval_pair, gStep_node, unpair_pair_fst]
        have hcertL : certL ≤ Nat.pair e (Nat.pair wit (Nat.pair certL certR)) :=
          le_trans (le_pair_left _ _)
            (le_trans (le_pair_right wit _) (le_pair_right e _))
        have hcertR : certR ≤ Nat.pair e (Nat.pair wit (Nat.pair certL certR)) :=
          le_trans (le_pair_right _ _)
            (le_trans (le_pair_right wit _) (le_pair_right e _))
        have hlt1 : Nat.pair a.unpair.1 certL < Nat.pair (2 * a + 2)
            (Nat.pair e (Nat.pair wit (Nat.pair certL certR))) :=
          pair_lt_pair_of_lt_le (by have := unpair_fst_le a; omega) hcertL
        have hlt2 : Nat.pair a.unpair.2 certR < Nat.pair (2 * a + 2)
            (Nat.pair e (Nat.pair wit (Nat.pair certL certR))) :=
          pair_lt_pair_of_lt_le (by have := unpair_snd_le a; omega) hcertR
        simp only [unpair_pair_fst, unpair_pair_snd]
        rw [listGet_rtbl_gEval fe fU fV mIdx hlt1, listGet_rtbl_gEval fe fU fV mIdx hlt2,
          gEval_out, gEval_out]
        rw [show (gEval fe fU fV mIdx (Nat.pair a.unpair.1 certL)).unpair.1 = 1 from hokL,
          show (gEval fe fU fV mIdx (Nat.pair a.unpair.2 certR)).unpair.1 = 1 from hokR]
        simp only [Nat.one_mul]
        exact hwit
      · rw [unpair_pair_fst]; exact he

end Computability
end Exercise717
end DomainTheory.Neighborhood
