module

public import DomainTheory.BridgeTheorems.toElement
public import DomainTheory.BridgeTheorems.ofElement
import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem ofElement_toElement (x : B.system.Element) :
    B.ofElement (B.toElement x) = x := by
  refine NeighborhoodSystem.Element.ext (V := B.system) fun X => ?_
  constructor
  · intro ⟨hX, i, hi, hsub⟩
    exact x.up_mem hi hX hsub
  · intro hX
    obtain ⟨i, rfl⟩ := B.exhaustive (x.sub hX)
    exact ⟨x.sub hX, i, hX, subset_rfl⟩

end NbhdBasis

end DomainTheory.BridgeTheorems
