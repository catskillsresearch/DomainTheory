module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem

@[expose] public section

section

namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

structure Element where

  mem : Set α → Prop

  sub : ∀ {X}, mem X → V.mem X

  master_mem : mem V.master

  inter_mem : ∀ {X Y}, mem X → mem Y → mem (X ∩ Y)

  up_mem : ∀ {X Y}, mem X → V.mem Y → X ⊆ Y → mem Y

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
