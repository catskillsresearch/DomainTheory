/-ai
Scott's Lemma 4.5 gives a criterion for projections out of the limit. If a sequence u, with u_n in stage n+1, satisfies the shifted recursion that the retraction at stage n+1 sends u_{n+1} to u_n, then the coordinate at stage n+1 of the supremum of the embeddings of the terms u_k is u_n.

The successor embeddings of the terms form a monotone family: the recursion rewrites the inclusion of u_k as the inclusion of a retraction, which lies below u at the next index, and the recursion equation for embeddings absorbs that inclusion. Any finite descent of a later term recovers u_n, by induction on the number of steps, peeling one retraction and applying the recursion. The coordinate at stage n+1 of the embedding of such a later term is therefore u_n, either because a component at its own stage is the element itself or because the component is that descent. The family is directed, so the projection from the limit preserves its supremum, and the desired coordinate is the supremum of the coordinates. Each of those coordinates is at most u_n, using monotonicity of the family when the index is below n. The coordinate at index n equals u_n, so the supremum equals u_n.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.embInf_succ

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))


/-- **Scott 1972, Lemma 4.5.** A criterion for recognizing projections out of the limit: if a
sequence `u : ∀ n, D_{n+1}` satisfies the (shifted) recursion `j_{n+1}(u_{n+2}) = u_{n+1}`, then the
monotone limit `u_∞ = ⨆ₙ i_{(n+1)∞}(uₙ)` has `j_{∞(n+1)}(u_∞) = uₙ`.

The proof follows Scott's argument at source lines 1316–1320.  First the defining family is
monotone.  Continuity of `j_{∞(n+1)}` therefore moves the projection through its directed
supremum.  Finally, for every `m ≥ n`, the identity
`j_{∞(n+1)}(i_{(m+1)∞}(u_m)) = u_n` is proved by induction on `m - n`, peeling one projection with
`projLE_succ` and then applying the recursion hypothesis `j_{m+1}(u_{m+1}) = u_m`. -/
theorem lemma_4_5 (u : ∀ n, D (n + 1))
    (hu : ∀ n, (P (n + 1)).retr (u (n + 1)) = u n) (n : ℕ) :
    (⨆ k, embInf D P (k + 1) (u k) : InverseLimit D P).1 (n + 1) = u n := by
  let a : ℕ → InverseLimit D P := fun k => embInf D P (k + 1) (u k)
  have ha_succ (k : ℕ) : a k ≤ a (k + 1) := by
    rw [show a k = embInf D P (k + 1) (u k) from rfl,
      show a (k + 1) = embInf D P (k + 2) (u (k + 1)) from rfl,
      ← embInf_succ D P (k + 1) (u k)]
    exact embInf_monotone D P (k + 2)
      (by calc (P (k + 1)).incl (u k)
            = (P (k + 1)).incl ((P (k + 1)).retr (u (k + 1))) := by rw [hu k]
          _ ≤ u (k + 1) := (P (k + 1)).incl_retr_le _)
  have ha : Monotone a := monotone_nat_of_le_succ ha_succ
  have hprojLE : ∀ d n : ℕ,
      projLE D P (show n + 1 ≤ n + d + 1 by omega) (u (n + d)) = u n := by
    intro d
    induction d with
    | zero =>
        intro n
        simpa only [Nat.add_zero] using
          (projLE_self D P (le_refl (n + 1)) (u n))
    | succ d ih =>
        intro n
        simp only [Nat.add_succ]
        rw [projLE_succ D P
          (show n + 1 ≤ n + d + 1 by omega)
          (show n + 1 ≤ (n + d + 1) + 1 by omega)]
        rw [hu (n + d)]
        exact ih n
  have hprojection : ∀ d n : ℕ,
      (embInf D P (n + d + 1) (u (n + d))).1 (n + 1) = u n := by
    intro d n
    cases d with
    | zero =>
        change iComp D P (n + 1) (u n) (n + 1) = u n
        exact iComp_self D P (n + 1) (u n)
    | succ d =>
        change iComp D P (n + (d + 1) + 1) (u (n + (d + 1))) (n + 1) = u n
        rw [iComp_of_ge D P (by omega)]
        exact hprojLE (d + 1) n
  have hdir : DirectedOn (· ≤ ·) (Set.range a) :=
    directedOn_range.2 ha.directed_le
  have hcont := (projInf D P (n + 1)).preservesDirectedSup_coe
    (Set.range a) (Set.range_nonempty a) hdir
  rw [show (⨆ k, embInf D P (k + 1) (u k) : InverseLimit D P)
      = sSup (Set.range a) from sSup_range.symm]
  change (projInf D P (n + 1)) (sSup (Set.range a)) = u n
  rw [hcont, ← Set.range_comp, sSup_range]
  apply le_antisymm
  · exact iSup_le fun m => by
      by_cases hmn : n ≤ m
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact le_of_eq (hprojection d n)
      · exact le_trans ((ha (Nat.le_of_not_ge hmn)) (n + 1))
          (le_of_eq (hprojection 0 n))
  · exact le_trans (le_of_eq (hprojection 0 n).symm) (le_iSup (fun m => (a m).1 (n + 1)) n)

end InverseLimit
end DomainTheory.ContinuousLattice
