/-ai
The set of projections is closed under binary joins. This is part of Scott's Proposition 3.12.

By the pointwise characterization, each of the two projections is idempotent and deflationary, and the same must be shown for their join. The join of their values at x lies below x. Monotonicity puts each map of that join below the corresponding value, while idempotence and monotonicity give the reverse inequalities. The pointwise formula for the join of maps therefore gives idempotence, and deflation is the same bound on the join of the values.
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
public import DomainTheory.ContinuousLattice.FunctionSpaces.sup_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.const_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_iff

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Projections

/-- `J_D` is closed under binary joins (Scott 1972, 3.12). The key step: since `j x ⊔ k x ⊑ x`,
monotonicity and idempotency force `j (j x ⊔ k x) = j x` and `k (j x ⊔ k x) = k x`. -/
theorem isProjection_sup {j k : ScottMap D D} (hj : IsProjection j) (hk : IsProjection k) :
    IsProjection (j ⊔ k) := by
  rw [isProjection_iff] at hj hk ⊢
  obtain ⟨hjidem, hjle⟩ := hj
  obtain ⟨hkidem, hkle⟩ := hk
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hjkle : (j : D → D) x ⊔ k x ≤ x := sup_le (hjle x) (hkle x)
    have hj_eq : (j : D → D) (j x ⊔ k x) = j x :=
      le_antisymm (j.monotone hjkle) (le_of_eq_of_le (hjidem x).symm (j.monotone le_sup_left))
    have hk_eq : (k : D → D) (j x ⊔ k x) = k x :=
      le_antisymm (k.monotone hjkle) (le_of_eq_of_le (hkidem x).symm (k.monotone le_sup_right))
    rw [ScottMap.sup_apply, ScottMap.sup_apply, hj_eq, hk_eq]
  · rw [ScottMap.sup_apply]; exact sup_le (hjle x) (hkle x)

end Projections

end DomainTheory.ContinuousLattice
