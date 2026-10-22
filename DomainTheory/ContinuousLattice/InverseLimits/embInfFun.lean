/-ai
The embedding of stage n into the inverse limit, as a bare function, sends x to the compatible sequence whose m-th coordinate climbs from x when m is at least n and descends from x when m is below n.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.iComp
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_compatible

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The embedding `i_{n∞} : Dₙ → D_∞` as a bare function into the inverse limit. -/
def embInfFun (n : ℕ) (x : D n) : InverseLimit D P := ⟨iComp D P n x, iComp_compatible D P n x⟩

end InverseLimit

end DomainTheory.ContinuousLattice
