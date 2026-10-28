module
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_le_of_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_apply
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem stepMap_wayBelow {e : D} {e' : D'} {f : ScottMap D D'}
    (he' : e' ≪ (f : D → D') e) : stepMap e e' ≪ f := by
  refine ⟨{g : ScottMap D D' | e' ≪ (g : D → D') e}, ⟨?_, ?_⟩, he', ?_⟩
  · intro g g' hgg' hg
    exact hg.trans_le (hgg' e)
  · intro F hFne hFdir hmem
    simp only [Set.mem_ofPred_eq, ScottMap.sSup_apply] at hmem
    have hne : (Set.image (fun g : ScottMap D D' => (g : D → D') e) F).Nonempty := hFne.image _
    have hdir : DirectedOn (· ≤ ·) (Set.image (fun g : ScottMap D D' => (g : D → D') e) F) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := hFdir a ha b hb
      exact ⟨(c : D → D') e, Set.mem_image_of_mem _ hc, hac e, hbc e⟩
    obtain ⟨_, ⟨g, hgF, rfl⟩, hg⟩ := (WayBelow.sSup_iff hne hdir).1 hmem
    exact ⟨g, hgF, hg⟩
  · intro g hg
    exact Set.mem_Ici.2 (stepMap_le_of_wayBelow hg)

end DomainTheory.ContinuousLattice
