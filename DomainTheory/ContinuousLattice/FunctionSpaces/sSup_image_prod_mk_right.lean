module
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
public import Mathlib.Order.ScottContinuity
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.FixedPoints

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem sSup_image_prod_mk_right (y : D') (S : Set D) (hS : S.Nonempty) :
    sSup (Set.image (fun x => (x, y)) S) = (sSup S, y) := by
  have himage : Set.image (fun x => (x, y)) S = S ×ˢ ({y} : Set D') := by
    ext ⟨a, b⟩
    simp only [Set.mem_image, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, h⟩
      obtain ⟨ha, hb⟩ := Prod.ext_iff.mp h
      subst ha
      exact ⟨hx, hb.symm⟩
    · rintro ⟨ha, hb⟩
      exact ⟨a, ha, Prod.ext_iff.mpr ⟨rfl, hb.symm⟩⟩
  have hy : sSup ({y} : Set D') = y := by
    apply le_antisymm
    · exact sSup_le fun z hz => by rw [Set.mem_singleton_iff] at hz; rw [hz]
    · exact le_sSup (Set.mem_singleton y)
  rw [himage, sSup_prod (hs := hS) (ht := ⟨y, Set.mem_singleton y⟩), hy]

end DomainTheory.ContinuousLattice
