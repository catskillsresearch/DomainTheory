/-ai
Selecting by a concatenation σ followed by τ equals selecting first by σ and then by τ.

Function extensionality reduces the trees to a continuation, and simplification uses associativity of append.
ai-/
module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}








/-- Composing selectors: `a(στ) = (aσ)τ`. -/
theorem select_append (a : Tree n) (σ τ : List (Fin n)) :
    select a (σ ++ τ) = select (select a σ) τ := by
  funext ρ; simp [List.append_assoc]

end Example62Regular
end DomainTheory.NeighbourhoodSystems
