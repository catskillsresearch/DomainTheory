module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Zorn
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
public import Mathlib.Topology.Inseparable

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
