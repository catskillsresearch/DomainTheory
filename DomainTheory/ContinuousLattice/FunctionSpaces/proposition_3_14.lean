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
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_unique

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
























































/-- **Scott 1972, Proposition 3.14.** For a continuous lattice `D` there is a uniquely determined
continuous mapping `fix : [D → D] → D` such that `f (fix f) = fix f` for all `f`, and `fix f ⊑ x`
whenever `f x ⊑ x`. Existence and continuity are `Proposition314.fixMap`; the defining equations are
`fix_eq`/`fix_le`; uniqueness (any operator with these two properties agrees with `fix`) is
`fix_unique`. -/
theorem proposition_3_14 (_hD : IsContinuousLattice D) :
    ∃ Fix : ScottMap (ScottMap D D) D,
      (∀ f : ScottMap D D, (f : D → D) (Fix f) = Fix f)
        ∧ (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → (Fix f : D) ≤ x)
        ∧ (∀ g : ScottMap D D → D,
            (∀ f : ScottMap D D, (f : D → D) (g f) = g f) →
            (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → g f ≤ x) →
            ∀ f : ScottMap D D, g f = Fix f) :=
  ⟨Proposition314.fixMap, fun f => Proposition314.fix_eq f,
    fun _ _ h => Proposition314.fix_le h,
    fun _ hfix hleast f => Proposition314.fix_unique (hfix f) (fun x hx => hleast f x hx)⟩

end DomainTheory.ContinuousLattice
