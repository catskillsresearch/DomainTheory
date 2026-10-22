module

public import Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Tree
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}

@[simp] theorem select_apply (a : Tree n) (σ τ : List (Fin n)) : select a σ τ = a (σ ++ τ) := rfl

end Example62Regular

end DomainTheory.NeighbourhoodSystems
