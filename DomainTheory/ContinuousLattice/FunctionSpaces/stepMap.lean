module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.preservesDirectedSup_coe
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_def
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_of_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_of_not_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_apply
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

noncomputable def stepMap (e : D) (e' : D') : ScottMap D D' :=
  ⟨stepFun e e', continuous_of_preservesDirectedSup (stepFun_preservesDirectedSup e e')⟩

namespace stepMap

theorem apply_of_wayBelow {e : D} {e' : D'} {x : D} (h : e ≪ x) :
    (stepMap e e' : D → D') x = e' :=
  stepFun_of_wayBelow h

theorem le_of_wayBelow {e : D} {e' : D'} {g : ScottMap D D'}
    (h : e' ≪ (g : D → D') e) : stepMap e e' ≤ g := by
  rw [ScottMap.le_def]
  intro x
  by_cases hex : e ≪ x
  · rw [apply_of_wayBelow hex]
    exact h.le.trans (g.monotone hex.le)
  · show stepFun e e' x ≤ (g : D → D') x
    rw [stepFun_of_not_wayBelow hex]
    exact bot_le

theorem wayBelow {e : D} {e' : D'} {f : ScottMap D D'}
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
    exact Set.mem_Ici.2 (le_of_wayBelow hg)

theorem pointwise_sSup (hD : ContinuousLattice D) (hD' : ContinuousLattice D') (f : ScottMap D D')
    (x : D) :
    sSup {e' : D' | ∃ e, e ≪ x ∧ e' ≪ (f : D → D') e} = (f : D → D') x := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro e' ⟨e, hex, he'⟩
    exact he'.le.trans (f.monotone hex.le)
  · rw [← hD'.sSup_wayBelow ((f : D → D') x)]
    refine sSup_le ?_
    intro w hw
    have hfx : (f : D → D') x = sSup (Set.image (f : D → D') {e | e ≪ x}) := by
      rw [← f.preservesDirectedSup_coe {e | e ≪ x} ⟨⊥, WayBelow.bot x⟩ (WayBelow.directedOn x),
        hD.sSup_wayBelow x]
    rw [hfx] at hw
    have hne : (Set.image (f : D → D') {e | e ≪ x}).Nonempty := ⟨f ⊥, ⊥, WayBelow.bot x, rfl⟩
    have hdir : DirectedOn (· ≤ ·) (Set.image (f : D → D') {e | e ≪ x}) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := WayBelow.directedOn x a ha b hb
      exact ⟨f c, Set.mem_image_of_mem _ hc, f.monotone hac, f.monotone hbc⟩
    obtain ⟨_, ⟨e, hex, rfl⟩, hwe⟩ := (WayBelow.sSup_iff hne hdir).1 hw
    exact le_sSup ⟨e, hex, hwe⟩

theorem isContinuousLattice (hD : ContinuousLattice D) (hD' : ContinuousLattice D') :
    ContinuousLattice (ScottMap D D') := by
  refine { out := ?_ }
  intro f
  refine ⟨fun h hh => hh.le, fun g hg => ?_⟩
  rw [ScottMap.le_def]
  intro x
  rw [← pointwise_sSup hD hD' f x]
  refine sSup_le ?_
  rintro e' ⟨e, hex, he'⟩
  have hle : stepMap e e' ≤ g := hg (wayBelow he')
  have hx := (ScottMap.le_def.1 hle) x
  rwa [apply_of_wayBelow hex] at hx

end stepMap

end DomainTheory.ContinuousLattice
