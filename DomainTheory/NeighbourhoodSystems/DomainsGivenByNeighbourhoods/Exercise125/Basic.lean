module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.finalSegmentSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.ofLowerSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.finalSegmentClassify
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.topElement
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.upperSet_subset_or
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.mem_def
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.master_eq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.Ici_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.exists_Ici_of_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf_isLowerSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.lowerSetOf_ofLowerSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.ofLowerSet_lowerSetOf

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem


variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]


variable [WellFoundedLT Δ]


omit [WellFoundedLT Δ]


theorem le_topElement (x : (finalSegmentSystem Δ).Element) : x ≤ topElement :=
  fun _ hX => x.sub hX

/-- **Exercise 1.25 — the unique total element.** The filter of all neighbourhoods is total
(`⊑`-maximal). -/
theorem topElement_isTotal : (finalSegmentSystem Δ).IsTotal (topElement (Δ := Δ)) :=
  fun y _ => le_topElement y

/-- It is the *unique* total element: any total `x` equals `topElement`. -/
theorem eq_topElement_of_isTotal {x : (finalSegmentSystem Δ).Element}
    (hx : (finalSegmentSystem Δ).IsTotal x) : x = topElement :=
  le_antisymm (le_topElement x) (hx topElement (le_topElement x))

/-- **Exercise 1.25 — not all elements are finite.** If `Δ` has *no greatest element* (e.g.
`Δ = ℕ = ω`), the total element `topElement` is not a principal filter `↑(Ici a)`: pick `b > a`,
then `Ici b ∈ topElement` but `Ici a ⊄ Ici b`. So `|𝒟|` has a non-finite (limit) element. -/
theorem topElement_not_principal_of_noMax (hnomax : ∀ a : Δ, ∃ b, a < b) (a : Δ) :
    topElement ≠ (finalSegmentSystem Δ).principal (Ici_mem a) := by
  intro h
  obtain ⟨b, hab⟩ := hnomax a
  have hmem : ((finalSegmentSystem Δ).principal (Ici_mem a)).mem (Set.Ici b) := by
    rw [← h]; exact Ici_mem b
  have hsub : Set.Ici a ⊆ Set.Ici b := hmem.2
  exact absurd (Set.Ici_subset_Ici.mp hsub) (not_le.mpr hab)
end FinalSegment
end DomainTheory.NeighbourhoodSystems
