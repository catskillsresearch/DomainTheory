module

public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst30
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_iff
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.preservesDirectedSup_coe
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Projections

theorem isProjection_directedSup {S : Set (ScottMap D D)} (hSne : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) (hS : ∀ j ∈ S, IsProjection j) :
    IsProjection (sSup S) := by
  have hidem : ∀ j ∈ S, ∀ x, (j : D → D) (j x) = j x :=
    fun j hj => (isProjection_iff.mp (hS j hj)).1
  have hle : ∀ j ∈ S, ∀ x, (j : D → D) x ≤ x := fun j hj => (isProjection_iff.mp (hS j hj)).2
  rw [isProjection_iff]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · set A := Set.image (fun j : ScottMap D D => (j : D → D) x) S with hA
    have hAne : A.Nonempty := hSne.image _
    have hAdir : DirectedOn (· ≤ ·) A := by
      rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
      obtain ⟨m, hm, hjm, hkm⟩ := hSdir j hj k hk
      exact ⟨(m : D → D) x, Set.mem_image_of_mem _ hm, hjm x, hkm x⟩
    have hsSx : ((sSup S : ScottMap D D) : D → D) x = sSup A := ScottMap.sSup_apply S x
    apply le_antisymm
    · rw [hsSx, ScottMap.sSup_apply]
      refine sSup_le ?_
      rintro _ ⟨k, hk, rfl⟩
      show (k : D → D) (sSup A) ≤ sSup A
      rw [k.preservesDirectedSup_coe A hAne hAdir]
      refine sSup_le ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      obtain ⟨m, hm, hjm, hkm⟩ := hSdir j hj k hk
      calc (k : D → D) (j x) ≤ (m : D → D) (j x) := hkm (j x)
        _ ≤ (m : D → D) (m x) := m.monotone (hjm x)
        _ = (m : D → D) x := hidem m hm x
        _ ≤ sSup A := le_sSup (Set.mem_image_of_mem _ hm)
    · rw [hsSx, ScottMap.sSup_apply]
      refine sSup_le ?_
      rintro _ ⟨j, hj, rfl⟩
      have hjxA : (j : D → D) x ≤ sSup A := le_sSup (Set.mem_image_of_mem _ hj)
      calc (j : D → D) x = (j : D → D) (j x) := (hidem j hj x).symm
        _ ≤ (j : D → D) (sSup A) := j.monotone hjxA
        _ ≤ sSup (Set.image (fun f : ScottMap D D => (f : D → D) (sSup A)) S) :=
              le_sSup (Set.mem_image_of_mem _ hj)
  · rw [ScottMap.sSup_apply]
    refine sSup_le ?_
    rintro _ ⟨j, hj, rfl⟩
    exact hle j hj x

end Projections

end DomainTheory.ContinuousLattice
