/-ai
The canonical Scott extension of a map into a continuous lattice is continuous for the Scott topology on the lattice.

If a Scott-open set contains the value at a point, the way-below basis supplies an element way-below that value whose principal upset lies in the open set. The value is a directed supremum of the defining family, so the element is way-below one of those infima, coming from an open neighbourhood of the point. The same neighbourhood witnesses that the element is way-below the value at every one of its points, so the neighbourhood lies in the preimage of the open set.
ai-/
module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
import all Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_aux_nonempty
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_aux_directed

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


section InjectiveExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]


omit [TopologicalSpace X] in
/-- The extension is Scott-continuous. For a Scott-open `U` and a point `y₀` with `g y₀ ∈ U`, the
basis lemma gives `a ≪ g y₀` with `↟a ⊆ U`; since `g y₀` is a directed supremum, `a ≪ ⊓ f''(e⁻¹V)`
for some open `V ∋ y₀`, and that value is `≤ g y'` for every `y' ∈ V`, so `V ⊆ g⁻¹U`. -/
theorem scottExtend_continuous (hE : IsContinuousLattice E) (e : X → Y) (f : X → E) :
    @Continuous Y E _ scottTopologicalSpace (scottExtend e f) := by
  let : TopologicalSpace E := scottTopologicalSpace
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_scottOpen] at hU
  rw [isOpen_iff_forall_mem_open]
  intro y₀ hy₀
  have hgy₀U : scottExtend e f y₀ ∈ U := hy₀
  obtain ⟨a, haz, hasub⟩ := exists_wayBelow_subset hE hU hgy₀U
  obtain ⟨d, hd, had⟩ := (wayBelow_sSup_iff (scottExtend_aux_nonempty e f y₀)
    (scottExtend_aux_directed e f y₀)).1 haz
  obtain ⟨V, hVo, hy₀V, rfl⟩ := hd
  refine ⟨V, ?_, hVo, hy₀V⟩
  intro y' hy'V
  show scottExtend e f y' ∈ U
  refine hasub ?_
  show a ≪ scottExtend e f y'
  exact had.trans_le (le_sSup ⟨V, hVo, hy'V, rfl⟩)

end InjectiveExtension
end DomainTheory.ContinuousLattice
