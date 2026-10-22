module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619

/-- **The one-point domain `{{Λ}} = 𝟙`** (the terminal object of Scott's category). -/
def Cone : ScottSys := singletonSys ({([] : Str)} : Set Str) ⟨[], rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
