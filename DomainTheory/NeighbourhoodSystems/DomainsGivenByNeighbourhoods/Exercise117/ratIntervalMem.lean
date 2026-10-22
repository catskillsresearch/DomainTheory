module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/-- A neighbourhood of `ratIntervalSystem`: either `Δ = ℝ`, or a non-empty open interval with
rational endpoints. -/
def ratIntervalMem (X : Set ℝ) : Prop :=
  X = Set.univ ∨ ∃ a b : ℚ, a < b ∧ X = Set.Ioo (a : ℝ) (b : ℝ)

end RatInterval

end DomainTheory.NeighbourhoodSystems
