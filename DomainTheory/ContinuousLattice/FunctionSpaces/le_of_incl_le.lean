module
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_sup_of_preservesSSup
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
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

variable {i : D → D'}

/-- From (i)+(ii): `i` is order-reflecting (`x ⊑ y ↔ i x ⊑ i y`), since `x ⊑ y ↔ x ⊔ y = y`. -/
theorem le_of_incl_le (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hinj : Function.Injective i) {x y : D} (h : i x ≤ i y) : x ≤ y := by
  have h1 : i (x ⊔ y) = i y := by rw [incl_sup_of_preservesSSup hi, sup_eq_right.mpr h]
  exact sup_eq_right.mp (hinj h1)

end Proposition310

end DomainTheory.ContinuousLattice
