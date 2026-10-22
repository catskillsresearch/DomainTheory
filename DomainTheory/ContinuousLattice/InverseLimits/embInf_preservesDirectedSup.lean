/-ai
The bare embedding of a stage into the inverse limit preserves directed suprema.

The image of a nonempty directed set under the embedding is nonempty, and it is directed because the embedding is monotone. The two inverse-limit elements agree once every coordinate agrees. At coordinate m, the coordinate of the supremum of the image is the supremum of the image of the coordinate functions. That image is the image under the m-th component of the climbing-and-descending sequence, which preserves the directed supremum.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.coe_sSup_of_directed
public import DomainTheory.ContinuousLattice.InverseLimits.iComp
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_preservesDirectedSup
public import DomainTheory.ContinuousLattice.InverseLimits.embInfFun
public import DomainTheory.ContinuousLattice.InverseLimits.embInfFun_coe
public import DomainTheory.ContinuousLattice.InverseLimits.embInf_monotone

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem embInf_preservesDirectedSup (n : ℕ) : PreservesDirectedSup (embInfFun D P n) := by
  intro S hS hSdir
  have hTne : (embInfFun D P n '' S).Nonempty := hS.image _
  have hTdir : DirectedOn (· ≤ ·) (embInfFun D P n '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨embInfFun D P n c, Set.mem_image_of_mem _ hc,
      embInf_monotone D P n hac, embInf_monotone D P n hbc⟩
  apply Subtype.ext
  rw [coe_sSup_of_directed D P (embInfFun D P n '' S) hTne hTdir]
  funext m
  have heq : Function.eval m '' (Subtype.val '' (embInfFun D P n '' S))
      = (fun x => iComp D P n x m) '' S := by
    simp only [Set.image_image, embInfFun_coe, Function.eval]
  rw [sSup_apply_eq_sSup_image, heq]
  exact iComp_preservesDirectedSup D P n m hS hSdir

end InverseLimit

end DomainTheory.ContinuousLattice
