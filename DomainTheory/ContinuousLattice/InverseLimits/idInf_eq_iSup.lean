/-ai
The identity Scott map on the inverse limit is the supremum, over n, of the composite of the stage embedding with the stage projection. This is the algebraic identity in the remark after Scott's Proposition 4.2, and it is the identity at the heart of Theorem 4.4.

On a compatible sequence x, the supremum of those composites evaluates as the supremum of their values at x, and that supremum is x because every inverse-limit element is the supremum of the embeddings of its coordinates.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_eq_iSup

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))


/-- **Scott 1972, §4 (functional equation, "the remark following 4.2").** The identity of `D_∞` is
the directed lub of the approximating projections `rₙ = i_{n∞} ∘ j_{∞n}`:
`id = ⨆ₙ i_{n∞} ∘ j_{∞n}`. This is the algebraic identity at the heart of Theorem 4.4. -/
theorem idInf_eq_iSup :
    (ScottMap.idMap : ScottMap (InverseLimit D P) (InverseLimit D P))
      = ⨆ n, (embInf D P n).comp (projInf D P n) := by
  apply ScottMap.ext
  intro x
  rw [show (⨆ n, (embInf D P n).comp (projInf D P n))
        = sSup (Set.range fun n => (embInf D P n).comp (projInf D P n)) from sSup_range.symm,
    ScottMap.sSup_apply, ScottMap.idMap_apply, ← Set.range_comp, sSup_range]
  exact inverseLimit_eq_iSup D P x

end InverseLimit
end DomainTheory.ContinuousLattice
