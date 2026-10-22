/-ai
If a map i between continuous lattices preserves arbitrary suprema, is injective, and preserves the way-below relation, then some continuous retraction makes the domain a projection of the codomain along i, and the retraction sends each ambient element to the supremum of the elements whose image lies below it. This is the converse half of Scott's Proposition 3.10.

The projection supplied by the converse construction has inclusion equal to i and retraction equal to that supremum, both by definition of the construction.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


section Proposition310

open Finset


variable {i : D → D'}


/-- **Scott 1972, Proposition 3.10 (converse).** If `i : D → D'` (between continuous lattices)
satisfies (i) preservation of arbitrary suprema, (ii) injectivity, and (iii) preservation of `≪`,
then there is a continuous `j` making `D` a projection of `D'` via `i`, with `j` given by Scott's
formula (iv) `j(x') = ⊔ { x | i(x) ⊑ x' }`. -/
theorem proposition_3_10_converse
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (hinj : Function.Injective i)
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : ContinuousLattice D) :
    ∃ P : IsContinuousLatticeProjection D D',
      (∀ d, (P.incl : D → D') d = i d)
        ∧ (∀ x', (P.retr : D' → D) x' = sSup {x | i x ≤ x'}) :=
  ⟨converseProjection hi hinj hwb hD, fun _ => rfl, fun _ => rfl⟩

end Proposition310
end DomainTheory.ContinuousLattice
