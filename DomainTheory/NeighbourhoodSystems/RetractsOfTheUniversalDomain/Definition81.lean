module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Retraction

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {E : NeighborhoodSystem α}


/-- The identity mapping `I_E` is (trivially) a retraction. -/
@[simp] theorem isRetraction_idMap : Retraction (idMap E) :=
  ⟨idMap_comp (idMap E)⟩

end DomainTheory.NeighbourhoodSystems
