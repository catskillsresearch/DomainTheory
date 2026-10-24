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


/-- `L_a` is genuinely `{σ ∣ pos(aσ) = true}` as Scott writes it. -/
theorem treeLang_eq_pos (a : Tree n) : treeLang a = {σ | pos (select a σ) = true} := by
  simp only [pos_select]; rfl

end Example62Regular
end DomainTheory.NeighbourhoodSystems
