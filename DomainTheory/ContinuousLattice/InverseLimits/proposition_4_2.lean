/-ai
Scott's Proposition 4.2 packages each stage as a projection of continuous lattices out of the inverse limit. The embedding is the Scott-continuous stage embedding, the retraction reads the stage coordinate, the retraction after the embedding is the identity because a component at its own stage is the original element, and the embedding after the retraction lies below the identity by the coordinatewise comparison of that embedding with the original sequence.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_self
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_incl_le
public import DomainTheory.ContinuousLattice.InverseLimits.embInfFun_coe
public import DomainTheory.ContinuousLattice.InverseLimits.embInf
public import DomainTheory.ContinuousLattice.InverseLimits.projInf

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- **Scott 1972, Proposition 4.2.** Each `j_{∞n} : D_∞ → Dₙ` is a projection of continuous
lattices, with embedding `i_{n∞} = embInf n`. -/
noncomputable def proposition_4_2 (n : ℕ) :
    IsContinuousLatticeProjection (D n) (InverseLimit D P) where
  incl := embInf D P n
  retr := projInf D P n
  retr_incl x := iComp_self D P n x
  incl_retr_le y := by
    rw [← Subtype.coe_le_coe]
    intro m
    exact iComp_incl_le D P n y m

end InverseLimit

end DomainTheory.ContinuousLattice
