module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.coconeInf_apply

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))


variable {D' : Type*} [CompleteLattice D']


/-- `f∞` is Scott-continuous: `f∞(⊔S) = ⊔ f∞(S)` for directed `S` (each `fₙ` is continuous and a
double `⨆` over `ℕ × S` commutes). -/
theorem coconeInf_preservesDirectedSup (f : ∀ n, ScottMap (D n) D') :
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
      eval_preservesDirectedSup D P n hS hSdir
    rw [h1, (f n).preservesDirectedSup_coe _ (hS.image _) (hev n), Set.image_image]
  show (⨆ n, f n ((sSup S).1 n)) = sSup (coconeInf D P f '' S)
  simp_rw [key, sSup_image', coconeInf_apply]
  rw [iSup_comm]

end InverseLimit
end DomainTheory.ContinuousLattice
