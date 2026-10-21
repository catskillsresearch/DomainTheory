/-ai
The subtree of a total tree selected by a word σ sends each continuation τ to the label of the original tree at σ appended to τ.
ai-/
module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Tree

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}

/-- Scott's subtree selector `σ ↦ aσ`: the subtree of `a` reached by the selector `σ`. Defined so
that `(aσ)τ = a(στ)`; the `pos`-label at node `τ` of `aσ` is the label at node `στ` of `a`. -/
def select (a : Tree n) (σ : List (Fin n)) : Tree n := fun τ => a (σ ++ τ)

end Example62Regular

end DomainTheory.NeighbourhoodSystems
