module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_bot
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

/-- Neighbourhood system of all `↟a`. -/
def toNeighborhoodSystem : NeighborhoodSystem D where
  mem X := ∃ a : D, X = wayBelowUp a
  master := Set.univ
  master_nonempty := ⟨⊥, Set.mem_univ _⟩
  master_mem := ⟨⊥, wayBelowUp_bot.symm⟩
  inter_mem := by
    intro X Y _Z hX hY _hZ _hZsub
    obtain ⟨a, rfl⟩ := hX
    obtain ⟨b, rfl⟩ := hY
    exact ⟨a ⊔ b, wayBelowUp_inter a b⟩
  sub_master := fun {_} _ => Set.subset_univ _

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
