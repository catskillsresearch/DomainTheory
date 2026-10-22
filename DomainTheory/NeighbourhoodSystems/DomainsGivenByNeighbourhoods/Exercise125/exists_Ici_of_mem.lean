module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.finalSegmentSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.mem_def
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.master_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

/-- **Well-order key lemma.** In a well-order, every non-empty upper set is `Set.Ici a`, where `a`
is its least element. -/
theorem exists_Ici_of_mem {X : Set Δ} (hX : (finalSegmentSystem Δ).mem X) :
    ∃ a, X = Set.Ici a := by
  obtain ⟨a, haX, hmin⟩ := wellFounded_lt.has_min X hX.1
  refine ⟨a, Set.ext fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · rcases lt_or_ge b a with hlt | hge
    · exact absurd hlt (hmin b hb)
    · exact hge
  · exact hX.2 (Set.mem_Ici.mp hb) haX

end FinalSegment

end DomainTheory.NeighbourhoodSystems
