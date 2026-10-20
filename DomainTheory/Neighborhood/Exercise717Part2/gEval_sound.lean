/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise717
public import DomainTheory.Neighborhood.Exercise510
public import DomainTheory.Neighborhood.Proposition77
public import DomainTheory.Neighborhood.Exercise717Part2.Basic
public import DomainTheory.Neighborhood.Exercise717Part2.pair_lt_pair_of_lt_le
public import DomainTheory.Neighborhood.Exercise717Part2.unpair_snd_snd_fst_le
public import DomainTheory.Neighborhood.Exercise717Part2.unpair_snd_snd_snd_le
public import DomainTheory.Neighborhood.Exercise717Part2.gStep_gamma
public import DomainTheory.Neighborhood.Exercise717Part2.gStep_leaf
public import DomainTheory.Neighborhood.Exercise717Part2.gStep_node
public import DomainTheory.Neighborhood.Exercise717Part2.gEval_pair
public import DomainTheory.Neighborhood.Exercise717Part2.listGet_rtbl_gEval
public import DomainTheory.Neighborhood.Exercise717Part2.gEval_out

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

















section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)



/-- **Soundness of the certificate.** If the memo certifies `⟨n, cert⟩` (ok-bit `1`), then `g` relates
`V_n` to `Q_{out}` (`out = cert.unpair.1`). Strong induction on the combined code `⟨n, cert⟩`; the node
case reads the two children from the memo table (`listGet_rtbl`) and applies the IH. -/
theorem gEval_sound
    (P : ComputablePresentation D) (Q : ComputablePresentation E)
    (hEq : ∀ m, fe (Nat.pair m mIdx) = 1 ↔ Q.X m = E.master)
    (hU : ∀ a m, (∃ i, fU (Nat.pair i (Nat.pair a m)) = 1) ↔ u.rel (P.X a) (Q.X m))
    (hV : ∀ k1 k2 m, (∃ i, fV (Nat.pair i (Nat.pair (Nat.pair k1 k2) m)) = 1) ↔
        v.rel (prodNbhd (Q.X k1) (Q.X k2)) (Q.X m)) :
    ∀ n cert, (gEval fe fU fV mIdx (Nat.pair n cert)).unpair.1 = 1 →
      GRel u v (Vsharp D P n) (Q.X cert.unpair.1) := by
  have key : ∀ w n cert, Nat.pair n cert = w →
      (gEval fe fU fV mIdx (Nat.pair n cert)).unpair.1 = 1 →
        GRel u v (Vsharp D P n) (Q.X cert.unpair.1) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro n cert hw hok
      rcases nat_shape n with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [gEval_pair, gStep_gamma, unpair_pair_fst] at hok
        rw [Vsharp_zero]
        exact GRel.gamma ((hEq cert.unpair.1).mp hok)
      · rw [gEval_pair, gStep_leaf, unpair_pair_fst] at hok
        rw [Vsharp_odd]
        exact GRel.leaf ((hU a cert.unpair.1).mp ⟨cert.unpair.2.unpair.1, hok⟩)
      · rw [Vsharp_even]
        rw [gEval_pair, gStep_node, unpair_pair_fst] at hok
        have hlt1 : Nat.pair a.unpair.1 cert.unpair.2.unpair.2.unpair.1 < Nat.pair (2 * a + 2) cert :=
          pair_lt_pair_of_lt_le (by have := unpair_fst_le a; omega) (unpair_snd_snd_fst_le cert)
        have hlt2 : Nat.pair a.unpair.2 cert.unpair.2.unpair.2.unpair.2 < Nat.pair (2 * a + 2) cert :=
          pair_lt_pair_of_lt_le (by have := unpair_snd_le a; omega) (unpair_snd_snd_snd_le cert)
        rw [listGet_rtbl_gEval fe fU fV mIdx hlt1,
          listGet_rtbl_gEval fe fU fV mIdx hlt2] at hok
        rw [nat_mul_eq_one, nat_mul_eq_one] at hok
        obtain ⟨⟨hokL, hokR⟩, hokV⟩ := hok
        have hgL := ih _ (hw ▸ hlt1) a.unpair.1 cert.unpair.2.unpair.2.unpair.1 rfl hokL
        have hgR := ih _ (hw ▸ hlt2) a.unpair.2 cert.unpair.2.unpair.2.unpair.2 rfl hokR
        rw [gEval_out, gEval_out] at hokV
        refine GRel.node hgL hgR ?_
        exact (hV _ _ cert.unpair.1).mp ⟨cert.unpair.2.unpair.1, hokV⟩
  intro n cert; exact key (Nat.pair n cert) n cert rfl

end Computability
end Exercise717
end DomainTheory.Neighborhood
