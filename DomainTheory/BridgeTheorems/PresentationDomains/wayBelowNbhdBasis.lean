module
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toNeighborhoodSystem
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_bot
public import DomainTheory.BridgeTheorems.NbhdBasis
public import Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice


@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open Order

open scoped DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

universe u

variable {D : Type u} [CompleteLattice D] [DecidableEq D]

/-- Decidable coding of the `↟`-neighbourhood system: tokens are elements of `D`. -/
def wayBelowNbhdBasis : NbhdBasis D D where
  system := toNeighborhoodSystem
  nbhd := wayBelowUp
  nbhd_mem := fun a => ⟨a, rfl⟩
  exhaustive := by
    intro X hX
    obtain ⟨a, rfl⟩ := hX
    exact ⟨a, rfl⟩
  botIdx := ⊥
  botIdx_eq := wayBelowUp_bot

end DomainTheory.BridgeTheorems
