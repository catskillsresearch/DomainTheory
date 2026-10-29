module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_unique
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_le
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_eq
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_preservesDirectedSup
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem proposition_3_14 (_hD : ContinuousLattice D) :
    ∃ Fix : ScottMap (ScottMap D D) D,
      (∀ f : ScottMap D D, (f : D → D) (Fix f) = Fix f)
        ∧ (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → (Fix f : D) ≤ x)
        ∧ (∀ g : ScottMap D D → D,
            (∀ f : ScottMap D D, (f : D → D) (g f) = g f) →
            (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → g f ≤ x) →
            ∀ f : ScottMap D D, g f = Fix f) :=
  ⟨fix.map, fun f => Proposition314.fix_eq f,
    fun _ _ h => Proposition314.fix_le h,
    fun _ hfix hleast f => Proposition314.fix_unique (hfix f) (fun x hx => hleast f x hx)⟩

end DomainTheory.ContinuousLattice
