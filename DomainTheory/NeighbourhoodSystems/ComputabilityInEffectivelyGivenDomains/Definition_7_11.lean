module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.finitePower

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

/-- Scott's Definition 7.11: finite joins and singletons in the powerdomain. -/
theorem definition_711 {α : Type*} (V : NeighborhoodSystem α) (x : V.Element) :
    V.PDsingleton x = V.PDfinJoin 1 (fun _ : Fin 1 => x) :=
  rfl

end DomainTheory.NeighbourhoodSystems
