/-ai
The infimum of a set of compatible sequences is a greatest lower bound for the coordinatewise order.

A member of the set lies below the infimum at each stage, because that coordinate of the infimum is the infimum of the corresponding coordinates. A lower bound lies below the infimum at each stage, because it is a lower bound of those coordinates.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem isGLB_sInf' (S : Set (InverseLimit D P)) :
    @IsGLB (InverseLimit D P)
      (inverseLimitPartialOrder D P).toPreorder.toLE S (sInf S) := by
  constructor
  · intro x hx n
    exact sInf_le (Set.mem_image_of_mem _ hx)
  · intro b hb n
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hb hx n

end InverseLimit

end DomainTheory.ContinuousLattice
