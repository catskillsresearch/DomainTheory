module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.fixedNbhd_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

instance instNonemptyMemSubtype (x : V.Element) : Nonempty {X : Set γ // x.mem X} :=
  ⟨⟨V.master, x.master_mem⟩⟩

end Algebraic

end DomainTheory.NeighbourhoodSystems
