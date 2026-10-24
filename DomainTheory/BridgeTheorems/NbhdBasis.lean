module
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainsGivenByNeighbourhoods
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23



@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems
open DomainTheory.InformationSystems

/-- A neighbourhood system with a decidable exhaustive index of its neighbourhoods.
`DecidableEq ι` is required so the induced information system can use choice-free
`Finset` operations (`InfoSys` tokens). -/
structure NbhdBasis (ι α : Type*) [DecidableEq ι] where
  system : NeighborhoodSystem α
  nbhd : ι → Set α
  nbhd_mem : ∀ i, system.mem (nbhd i)
  exhaustive : ∀ {X : Set α}, system.mem X → ∃ i, nbhd i = X
  botIdx : ι
  botIdx_eq : nbhd botIdx = system.master

end DomainTheory.BridgeTheorems
