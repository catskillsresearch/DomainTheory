module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


/-- Each pointwise-subbasic set `{f | f x ∈ U}` (`U` Scott-open) is Scott-open in the lattice
`[D → D']`, because suprema there are pointwise. This is the easy inclusion pointwise ⊆ Scott. -/
theorem pointwiseSubbasic_scottOpen (x : D) {U : Set D'} (hU : ScottOpen U) :
    ScottOpen {f : ScottMap D D' | (f : D → D') x ∈ U} := by
  refine ⟨fun f f' hff' hf => hU.1 (hff' x) hf, fun F hFne hFdir hmem => ?_⟩
  simp only [Set.mem_ofPred_eq, ScottMap.sSup_apply] at hmem
  have hne : (Set.image (fun g : ScottMap D D' => (g : D → D') x) F).Nonempty := hFne.image _
  have hdir : DirectedOn (· ≤ ·) (Set.image (fun g : ScottMap D D' => (g : D → D') x) F) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hFdir a ha b hb
    exact ⟨(c : D → D') x, Set.mem_image_of_mem _ hc, hac x, hbc x⟩
  obtain ⟨_, ⟨g, hgF, rfl⟩, hg⟩ := hU.2 hne hdir hmem
  exact ⟨g, hgF, hg⟩

end DomainTheory.ContinuousLattice
