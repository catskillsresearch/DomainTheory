module

public import Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.pos
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.child
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.treeLang
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.EventuallyPeriodic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Tree
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.pos_select
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.mem_treeLang

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
