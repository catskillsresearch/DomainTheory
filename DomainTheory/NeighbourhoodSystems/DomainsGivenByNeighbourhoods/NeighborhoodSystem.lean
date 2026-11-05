module

public import Mathlib.Data.Set.Defs

@[expose] public section

section

namespace DomainTheory.NeighbourhoodSystems

structure NeighborhoodSystem (α : Type*) where

  mem : Set α → Prop

  master : Set α

  master_nonempty : master.Nonempty

  master_mem : mem master

  inter_mem : ∀ {X Y Z : Set α}, mem X → mem Y → mem Z → Z ⊆ X ∩ Y → mem (X ∩ Y)

  sub_master : ∀ {X : Set α}, mem X → X ⊆ master

end DomainTheory.NeighbourhoodSystems
end
