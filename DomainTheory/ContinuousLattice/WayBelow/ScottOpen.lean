module

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

def ScottOpen (U : Set D) : Prop :=
  open CompleteLattice in
  letI : LE D := (toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : SupSet D := (toCompleteSemilatticeSup (α := D)).toSupSet
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty

namespace ScottOpen

theorem isUpperSet {U : Set D} (h : ScottOpen U) : IsUpperSet U := h.1

theorem inter {U V : Set D} (hU : ScottOpen U) (hV : ScottOpen V) : ScottOpen (U ∩ V) := by
  refine ⟨hU.1.inter hV.1, fun S hS hSdir hmem => ?_⟩
  obtain ⟨s₁, hs₁S, hs₁U⟩ := hU.2 hS hSdir hmem.1
  obtain ⟨s₂, hs₂S, hs₂V⟩ := hV.2 hS hSdir hmem.2
  obtain ⟨s₃, hs₃S, h₁, h₂⟩ := hSdir s₁ hs₁S s₂ hs₂S
  exact ⟨s₃, hs₃S, hU.1 h₁ hs₁U, hV.1 h₂ hs₂V⟩

theorem univ : ScottOpen (Set.univ : Set D) := by
  refine ⟨isUpperSet_univ, fun S hS _ _ => ?_⟩
  obtain ⟨s, hs⟩ := hS
  exact ⟨s, hs, Set.mem_univ s⟩

theorem sUnion {C : Set (Set D)} (hC : ∀ U ∈ C, ScottOpen U) : ScottOpen (⋃₀ C) := by
  refine ⟨isUpperSet_sUnion fun U hU => (hC U hU).1, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hUC, hUmem⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := (hC U hUC).2 hS hSdir hUmem
  exact ⟨s, hsS, U, hUC, hsU⟩

theorem iff_dirSupInacc {U : Set D} : ScottOpen U ↔ IsUpperSet U ∧ DirSupInacc U := by
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

theorem isOpen_iff {U : Set D} : @IsOpen D scottTopologicalSpace U ↔ ScottOpen U := by
  rw [iff_dirSupInacc, scottTopologicalSpace]
  have hinst : @IsScott D (@Set.univ (Set D)) _ (Topology.scott D (@Set.univ (Set D))) :=
    @IsScott.mk D (@Set.univ (Set D)) _ (Topology.scott D (@Set.univ (Set D))) rfl
  simpa [dirSupInaccOn_univ] using
    @IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn D (@Set.univ (Set D)) _
      (Topology.scott D (@Set.univ (Set D))) U hinst

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]

variable {x : ι → D} {L y : D}

theorem not_le (L : D) : ScottOpen {z : D | ¬ z ≤ L} := by
  refine ⟨fun a b hab ha hb => ha (le_trans hab hb), fun S hSne hSdir hmem => ?_⟩
  by_contra hcon
  refine hmem (sSup_le fun s hs => ?_)
  by_contra hsL
  exact hcon ⟨s, hs, hsL⟩

theorem wayBelow (x : D) :
    ScottOpen {z : D | ∃ U : Set D, ScottOpen U ∧ z ∈ U ∧ U ⊆ Set.Ici x} := by
  refine ⟨fun a b hab ha => ?_, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hU, haU, hsub⟩ := ha
  exact ⟨U, hU, hU.1 hab haU, hsub⟩
  obtain ⟨U, hU, hsupU, hsub⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
  exact ⟨s, hsS, ⟨U, hU, hsU, hsub⟩⟩

end ScottOpen

end DomainTheory.ContinuousLattice
