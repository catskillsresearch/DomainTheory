module

public import Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Tree
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}

@[simp] theorem select_nil (a : Tree n) : select a [] = a := by
  funext τ; simp

end Example62Regular

end DomainTheory.NeighbourhoodSystems
