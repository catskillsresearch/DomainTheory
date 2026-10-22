module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_le_algHom

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))


theorem descMap_le_algHom (g : AlgHom (ExpAlg N hN) B) : descMap hN B ≤ g.hom.1 := by
  intro X Y hr
  obtain ⟨n, hn⟩ := hr
  exact descRel_le_algHom hN B g n X Y hn

end Existence
end Exercise619
end DomainTheory.NeighbourhoodSystems
