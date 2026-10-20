module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
import all Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
import all Mathlib.Order.FixedPoints
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

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

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
