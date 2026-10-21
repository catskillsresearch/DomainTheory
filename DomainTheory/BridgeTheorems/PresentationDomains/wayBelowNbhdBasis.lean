/-ai
The way-below neighbourhood basis on a complete lattice with decidable equality takes the way-below neighbourhood system, indexes neighbourhoods by elements through the principal way-below neighbourhoods, and takes bottom as the index of the master neighbourhood. Each principal way-below neighbourhood is a neighbourhood, witnessed by its element, and every neighbourhood of the system is the way-below neighbourhood of the element that presents it. The way-below neighbourhood of bottom is the master neighbourhood.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice

@[expose] public section

set_option linter.unusedSectionVars false

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
