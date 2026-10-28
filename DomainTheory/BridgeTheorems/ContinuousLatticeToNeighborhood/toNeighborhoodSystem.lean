module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_inter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

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
