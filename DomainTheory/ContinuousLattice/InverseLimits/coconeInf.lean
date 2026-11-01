module

public import DomainTheory.ContinuousLattice.InverseLimits.embInf

import DomainTheory.ContinuousLattice.InverseLimits.limitProjectionToLevel
@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

variable {D' : Type*} [CompleteLattice D']

def coconeInf (f : ∀ n, ScottMap (D n) D') (x : InverseLimit D P) : D' :=
  ⨆ n, f n (x.1 n)

namespace coconeInf

theorem apply (f : ∀ n, ScottMap (D n) D') (x : InverseLimit D P) :
    coconeInf D P f x = ⨆ n, f n (x.1 n) := rfl

theorem climb (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) {n : ℕ} (x : D n) :
    ∀ {m : ℕ} (h : n ≤ m), f m (embeddingAlongTower D P h x) = f n x := by
  intro m h
  induction m, h using Nat.le_induction with
  | base => rw [embeddingAlongTower.self]
  | succ k hk ih =>
      rw [embeddingAlongTower.succ D P hk (Nat.le_succ_of_le hk), ← hf k, ih]

theorem descend (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) {m : ℕ} :
    ∀ {n : ℕ} (h : m ≤ n) (x : D n), f m (projectionAlongTower D P h x) ≤ f n x := by
  intro n h
  induction n, h using Nat.le_induction with
  | base =>
      intro x
      exact le_of_eq (congrArg (f m) (projectionAlongTower.self D P (le_refl m) x))
  | succ k hk ih =>
      intro x
      rw [projectionAlongTower.succ D P hk (Nat.le_succ_of_le hk)]
      calc f m (projectionAlongTower D P hk ((P k).retr x)) ≤ f k ((P k).retr x) := ih ((P k).retr x)
        _ = f (k + 1) ((P k).incl ((P k).retr x)) := hf k _
        _ ≤ f (k + 1) x := (f (k + 1)).monotone ((P k).incl_retr_le x)

theorem comp_embInf (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) (n : ℕ) (x : D n) :
    coconeInf D P f (embInf D P n x) = f n x := by
  apply le_antisymm
  · show (⨆ m, f m ((embInf D P n x).1 m)) ≤ f n x
    refine iSup_le fun m => ?_
    show f m (iComp D P n x m) ≤ f n x
    by_cases h : n ≤ m
    · rw [iComp_of_le D P h]; exact le_of_eq (climb D P f hf x h)
    · rw [iComp_of_ge D P h]; exact descend D P f hf (le_of_lt (not_le.mp h)) x
  · refine le_trans (le_of_eq ?_) (le_iSup (fun m => f m ((embInf D P n x).1 m)) n)
    rw [show (embInf D P n x).1 n = x from iComp_self D P n x]

theorem preservesDirectedSup (f : ∀ n, ScottMap (D n) D') :
    PreservesDirectedSup (coconeInf D P f) := by
  intro S hS hSdir
  have hev : ∀ n, DirectedOn (· ≤ ·) ((fun s : InverseLimit D P => s.1 n) '' S) := by
    intro n
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨c.1 n, ⟨c, hc, rfl⟩, hac n, hbc n⟩
  have key : ∀ n, f n ((sSup S).1 n) = sSup ((fun s : InverseLimit D P => f n (s.1 n)) '' S) := by
    intro n
    have h1 : (sSup S).1 n = sSup ((fun s : InverseLimit D P => s.1 n) '' S) :=
      (limitProjectionToLevel.preservesDirectedSup D P n) hS hSdir
    rw [h1, (f n).preservesDirectedSup_coe _ (hS.image _) (hev n), Set.image_image]
  show (⨆ n, f n ((sSup S).1 n)) = sSup (coconeInf D P f '' S)
  simp_rw [key, sSup_image', apply]
  rw [iSup_comm]

end coconeInf

end InverseLimit

end DomainTheory.ContinuousLattice
