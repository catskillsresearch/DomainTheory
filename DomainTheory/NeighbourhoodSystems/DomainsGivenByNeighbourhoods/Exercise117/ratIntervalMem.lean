/-ai
A set of reals is a rational-interval neighbourhood when it is the whole real line, or when it is a nonempty open interval with rational endpoints.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Real.Basic
import all Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import all Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

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
