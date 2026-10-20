module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem








/-- The atom `↑{n}` (a finite element). -/
theorem flat_mem_singleton (n : ℕ) : flat.mem {n} := Or.inr ⟨n, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise115
