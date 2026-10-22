module

public import DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
public import DomainTheory.ContinuousLattice.Specialization.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]


theorem ScottOpen_iff_dirSupInacc {U : Set D} : ScottOpen U ↔ IsUpperSet U ∧ DirSupInacc U := by
  constructor
  · intro ⟨hU, hU'⟩
    refine ⟨hU, fun d hd₁ hd₂ a ha hmem => ?_⟩
    rw [← IsLUB.sSup_eq ha] at hmem
    obtain ⟨s, hs, hsU⟩ := hU' hd₁ hd₂ hmem
    exact ⟨s, hs, hsU⟩
  · intro ⟨hU, hU'⟩
    refine ⟨hU, fun d hd₁ hd₂ hmem => ?_⟩
    obtain ⟨s, hs, hsU⟩ := hU' hd₁ hd₂ (isLUB_sSup d) hmem
    exact ⟨s, hs, hsU⟩

end DomainTheory.ContinuousLattice
