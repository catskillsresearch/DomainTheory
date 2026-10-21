/-ai
The filter associated with a nonempty lower set consists of the neighbourhoods that contain the principal upper set of some member of the set. Subfamily membership is the neighbourhood conjunct. The master belongs because some member of the set has its principal upper set contained in the whole token set, which is a nonempty upper set. For an intersection, the principal upper set of the maximum of the two witnesses is contained in each neighbourhood, since the maximum lies above both witnesses, and hence is contained in the intersection. That principal upper set is a neighbourhood, so the intersection law applies, and the maximum lies in the set because it equals one of the two witnesses. Upward closure keeps the same witness and composes the inclusions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
import all Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.finalSegmentSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.mem_def
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.master_eq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.Ici_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

/-- The filter built from a non-empty lower set `S`: the neighbourhoods that contain some
`Ici a` with `a ∈ S`. -/
def ofLowerSet (S : Set Δ) (hSne : S.Nonempty) (_hS : IsLowerSet S) :
    (finalSegmentSystem Δ).Element where
  mem X := (finalSegmentSystem Δ).mem X ∧ ∃ a ∈ S, Set.Ici a ⊆ X
  sub h := h.1
  master_mem := by
    obtain ⟨a, ha⟩ := hSne
    exact ⟨⟨Set.univ_nonempty, isUpperSet_univ⟩, a, ha, Set.subset_univ _⟩
  inter_mem := by
    rintro X Y ⟨hX, a, haS, haX⟩ ⟨hY, b, hbS, hbY⟩
    have hsub : Set.Ici (max a b) ⊆ X ∩ Y :=
      Set.subset_inter
        ((Set.Ici_subset_Ici.mpr (le_max_left a b)).trans haX)
        ((Set.Ici_subset_Ici.mpr (le_max_right a b)).trans hbY)
    refine ⟨(finalSegmentSystem Δ).inter_mem hX hY (Ici_mem (max a b)) hsub, max a b, ?_, hsub⟩
    rcases max_choice a b with h | h
    · rw [h]; exact haS
    · rw [h]; exact hbS
  up_mem := by
    rintro X Y ⟨_, a, haS, haX⟩ hY hXY
    exact ⟨hY, a, haS, haX.trans hXY⟩

end FinalSegment

end DomainTheory.NeighbourhoodSystems
