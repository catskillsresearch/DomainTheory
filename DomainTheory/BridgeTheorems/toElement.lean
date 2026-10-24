module

public import DomainTheory.BridgeTheorems.toInfoSys
public import DomainTheory.BridgeTheorems.filter_mem_interOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainsGivenByNeighbourhoods
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Element
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf_empty

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- Filter → InfoSys element. -/
def toElement (x : B.system.Element) : B.toInfoSys.Element where
  carrier := {i | x.mem (B.nbhd i)}
  consistent := fun Y hY => x.sub (B.filter_mem_interOf x hY)
  closed := by
    intro Y a hY ⟨_, hsub⟩
    exact x.up_mem (B.filter_mem_interOf x hY) (B.nbhd_mem a) hsub

end NbhdBasis

end DomainTheory.BridgeTheorems
