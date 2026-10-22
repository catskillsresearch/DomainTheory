/-ai
For an element x and a nonempty set S, the supremum of the pairs with left coordinate x and right coordinate in S equals the pair of x with the supremum of S.

The set of such pairs is the product of the singleton of x with S. The supremum of that singleton is x, because every member equals x and x belongs to the singleton. The supremum of a product of nonempty sets is the pair of the suprema.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst28
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst30
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.const_apply

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem sSup_image_prod_mk_left (x : D) (S : Set D') (hS : S.Nonempty) :
    sSup (Set.image (fun y => (x, y)) S) = (x, sSup S) := by
  have himage : Set.image (fun y => (x, y)) S = ({x} : Set D) ×ˢ S := by
    ext ⟨a, b⟩
    simp only [Set.mem_image, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, h⟩
      obtain ⟨ha, hb⟩ := Prod.ext_iff.mp h
      subst hb
      exact ⟨ha.symm, hy⟩
    · rintro ⟨ha, hb⟩
      refine ⟨b, hb, Prod.ext_iff.mpr ⟨ha.symm, rfl⟩⟩
  have hx : sSup ({x} : Set D) = x := by
    apply le_antisymm
    · exact sSup_le fun z hz => by rw [Set.mem_singleton_iff] at hz; rw [hz]
    · exact le_sSup (Set.mem_singleton x)
  rw [himage, sSup_prod (hs := ⟨x, Set.mem_singleton x⟩) (ht := hS), hx]

end DomainTheory.ContinuousLattice
