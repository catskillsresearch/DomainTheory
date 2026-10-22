module

public import Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}


/-- **Scott's selector recursion, step `a(iσ) = (aᵢ)σ`.** Reading the digit `i` then `σ` is the same
as descending to the `i`-th child `aᵢ` and reading `σ` there. -/
theorem select_cons (a : Tree n) (i : Fin n) (σ : List (Fin n)) :
    select a (i :: σ) = select (child a i) σ := by
  funext τ; simp [child]

end Example62Regular
end DomainTheory.NeighbourhoodSystems
