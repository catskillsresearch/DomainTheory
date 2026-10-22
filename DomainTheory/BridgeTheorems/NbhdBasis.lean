/-ai
A neighbourhood basis, indexed by a type with decidable equality, consists of a neighbourhood system, a neighbourhood for each index, a proof that each of these sets is a neighbourhood, a proof that every neighbourhood arises under some index, and a bottom index whose neighbourhood is the master set of the system. Decidable equality of the index is what lets the induced information system use choice-free finite-set operations on tokens.
ai-/
module


public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
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
