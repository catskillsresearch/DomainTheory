module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeRetractionProjection
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

variable {D : Type*} [CompleteLattice D]

namespace ProjectionSpace

/-- Scott's Def. 3.11: $j \in [D \to D]$ with $j \circ j = j$ and $j \sqsubseteq \mathrm{id}$. -/
def mem (j : ScottMap D D) : Prop :=
  j.comp j = j ∧ j ≤ ScottMap.idMap

theorem iff {j : ScottMap D D} :
    mem j ↔ (∀ x, (j : D → D) (j x) = j x) ∧ (∀ x, (j : D → D) x ≤ x) := by
  constructor
  · rintro ⟨hidem, hle⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have h : ((j.comp j : ScottMap D D) : D → D) x = (j : D → D) x := by rw [hidem]
      rwa [ScottMap.comp_apply] at h
    · have h := (ScottMap.le_def.mp hle) x
      rwa [ScottMap.idMap_apply] at h
  · rintro ⟨hidem, hle⟩
    exact ⟨ScottMap.ext fun x => by rw [ScottMap.comp_apply]; exact hidem x,
      ScottMap.le_def.mpr fun x => by rw [ScottMap.idMap_apply]; exact hle x⟩

theorem bot_mem : mem (⊥ : ScottMap D D) := by
  rw [iff]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · simp only [ScottMap.bot_apply]
  · rw [ScottMap.bot_apply]; exact bot_le

theorem sup_mem {j k : ScottMap D D} (hj : mem j) (hk : mem k) : mem (j ⊔ k) := by
  rw [iff] at hj hk ⊢
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

theorem directedSup_mem {S : Set (ScottMap D D)} (hSne : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) (hS : ∀ j ∈ S, mem j) : mem (sSup S) := by
  have hidem : ∀ j ∈ S, ∀ x, (j : D → D) (j x) = j x := fun j hj => (iff.mp (hS j hj)).1
  have hle : ∀ j ∈ S, ∀ x, (j : D → D) x ≤ x := fun j hj => (iff.mp (hS j hj)).2
  rw [iff]
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

theorem finsetSup_mem {T : Finset (ScottMap D D)} (hT : ∀ j ∈ T, mem j) :
    mem (T.sup id) :=
  Finset.sup_induction bot_mem (fun _ ha _ hb => sup_mem ha hb) hT

theorem sSup_mem {T : Set (ScottMap D D)} (hT : ∀ j ∈ T, mem j) : mem (sSup T) := by
  rw [ContinuousLatticeProjection.sSup_finsetSupOf T]
  refine directedSup_mem ⟨⊥, ∅, by simp, by simp⟩
    (ContinuousLatticeProjection.directedOn_finsetSupOf T) ?_
  rintro z ⟨F, hF, rfl⟩
  exact finsetSup_mem fun j hj => hT j (hF j hj)

end ProjectionSpace

/-- Scott's projection space $J_D$ (Definition 3.11). -/
abbrev ProjectionSpace (D : Type*) [CompleteLattice D] : Type _ :=
  { j : ScottMap D D // ProjectionSpace.mem j }

namespace ProjectionSpace

noncomputable instance instSupSet : SupSet (ProjectionSpace D) :=
  ⟨fun T => ⟨sSup (Set.image Subtype.val T), sSup_mem (by rintro j ⟨p, _, rfl⟩; exact p.2)⟩⟩

theorem isLUB_sSup (T : Set (ProjectionSpace D)) : IsLUB T (sSup T) := by
  constructor
  · intro p hp
    apply Subtype.coe_le_coe.mp
    show (p : ScottMap D D) ≤ ((sSup T : ProjectionSpace D) : ScottMap D D)
    exact le_sSup (Set.mem_image_of_mem _ hp)
  · intro q hq
    apply Subtype.coe_le_coe.mp
    show ((sSup T : ProjectionSpace D) : ScottMap D D) ≤ (q : ScottMap D D)
    refine sSup_le ?_
    rintro _ ⟨p, hp, rfl⟩
    exact Subtype.coe_le_coe.mpr (hq hp)

noncomputable instance instCompleteLattice : CompleteLattice (ProjectionSpace D) :=
  completeLatticeOfSup (ProjectionSpace D) isLUB_sSup

end ProjectionSpace

end DomainTheory.ContinuousLattice
