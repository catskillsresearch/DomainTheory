module
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Finset.Basic


@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


section Proposition310

open Finset

namespace IsContinuousLatticeProjection


/-- **Scott 1972, Proposition 3.10(iv), uniqueness.** The retraction of any projection is forced to
be Scott's formula `j(x') = ⊔ { x | i(x) ⊑ x' }`. `≤`: `j(x')` itself satisfies `i(j x') ⊑ x'`
(by `i ∘ j ⊑ id`), so it is a member of the set; `≥`: each member `x` (with `i x ⊑ x'`) satisfies
`x = j(i x) ⊑ j(x')` by `j ∘ i = id` and monotonicity. -/
theorem retr_eq_sSup (P : IsContinuousLatticeProjection D D') (x' : D') :
    (P.retr : D' → D) x' = sSup {x | (P.incl : D → D') x ≤ x'} := by
  apply le_antisymm
  · exact le_sSup (show (P.incl : D → D') (P.retr x') ≤ x' from P.incl_retr_le x')
  · refine sSup_le fun x hx => ?_
    calc x = (P.retr : D' → D) (P.incl x) := (P.retr_incl x).symm
      _ ≤ (P.retr : D' → D) x' := P.retr.monotone hx

end IsContinuousLatticeProjection
end Proposition310
end DomainTheory.ContinuousLattice
