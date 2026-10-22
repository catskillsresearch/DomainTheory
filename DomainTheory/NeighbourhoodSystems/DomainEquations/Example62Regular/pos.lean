module

public import Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Tree

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}

/-- Scott's `pos : A → T`: the `±` label at the **root** of the tree (`pos(±⟨…⟩) = true/false`). -/
def pos (a : Tree n) : Bool := a []

end Example62Regular

end DomainTheory.NeighbourhoodSystems
