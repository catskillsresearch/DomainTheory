module

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

theorem scottTopology_prop :
    (scottTopologicalSpace : TopologicalSpace Prop) = sierpinskiSpace := by
  apply le_antisymm
  ·
    show (scottTopologicalSpace : TopologicalSpace Prop) ≤ TopologicalSpace.generateFrom {{True}}
    apply le_generateFrom
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rw [ScottOpen.isOpen_iff]
    refine ⟨?_, ?_⟩
    · intro a b hab ha
      rw [Set.mem_singleton_iff] at ha ⊢
      exact le_antisymm le_top (ha ▸ hab)
    · intro S _ _ hmem
      rw [Set.mem_singleton_iff] at hmem
      have hex : ∃ p ∈ S, p := by rw [← sSup_Prop_eq, hmem]; trivial
      obtain ⟨p, hpS, hp⟩ := hex
      exact ⟨p, hpS, by rw [Set.mem_singleton_iff]; exact eq_true hp⟩
  ·
    rw [TopologicalSpace.le_def]
    intro U hU
    rw [ScottOpen.isOpen_iff] at hU
    by_cases hT : True ∈ U
    · by_cases hF : False ∈ U
      · have hUuniv : U = Set.univ := by
          ext p
          simp only [Set.mem_univ, iff_true]
          by_cases hp : p
          · rwa [eq_true hp]
          · rwa [eq_false hp]
        rw [hUuniv]; exact isOpen_univ
      · have hUtrue : U = {True} := by
          ext p
          rw [Set.mem_singleton_iff]
          constructor
          · intro hpU
            by_cases hp : p
            · exact eq_true hp
            · exact absurd (eq_false hp ▸ hpU) hF
          · intro hp; rw [hp]; exact hT
        rw [hUtrue]; exact isOpen_singleton_true
    · have hUempty : U = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hpU
        exact hT (hU.1 le_top hpU)
      rw [hUempty]; exact isOpen_empty

end DomainTheory.ContinuousLattice
