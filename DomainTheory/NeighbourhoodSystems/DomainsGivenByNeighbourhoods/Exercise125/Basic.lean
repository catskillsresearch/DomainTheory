/-ai
Every element of the final-segment system approximates the filter of all neighbourhoods.

A neighbourhood belonging to the element is a neighbourhood, so it belongs to the filter of all neighbourhoods.

The filter of all neighbourhoods is total.

Any element above it remains below it, by the comparison of an arbitrary element with that filter.

A total element equals the filter of all neighbourhoods.

The element lies below that filter, and totality applied to the filter, which lies above the element, gives the reverse comparison.

If the token order has no greatest element, the filter of all neighbourhoods is distinct from the principal filter of every principal final segment.

Given a point strictly above the generator of such a segment, the principal final segment of the higher point belongs to the filter of all neighbourhoods, hence to that principal filter, so the lower segment is contained in the higher one. A strict increase rules out that containment.
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

/-!
# Exercise 1.25 (Scott 1981, PRG-19, §1) — final segments of an ordinal

Scott: let `Δ` be a well-ordered set (ordinal) and let `𝒟` be the family of non-empty *final*
segments of `Δ`. Describe `|𝒟|`; are all elements finite; is every approximation to a finite
element finite?

For a linear order, the *final segments* are exactly the non-empty **upper sets** (`IsUpperSet`).
Any two upper sets of a linear order are nested (`upperSet_subset_or`), so the family is a
neighbourhood system by Scott's nested-or-disjoint criterion (`finalSegmentSystem`).

**Classification of `|𝒟|`.** For a *well-order* every non-empty upper set is `Set.Ici a` with `a`
its minimum (`exists_Ici_of_mem`). Hence a filter `x` is completely described by its trace
`lowerSetOf x = {a ∣ Ici a ∈ x}`, which is a **non-empty lower set** of `Δ`, and `x ↦ lowerSetOf x`
is an order isomorphism

`|𝒟| ≃o {S : Set Δ ∣ S non-empty lower set}` (ordered by `⊆`)   — `finalSegmentClassify`.

So `|𝒟|` is the lattice of non-empty initial segments of `Δ` (the "cuts" of `Δ`).

**Total / finite.** The greatest element is the filter of *all* neighbourhoods (`topElement`),
which is the unique total element (`topElement_isTotal`, `eq_topElement_of_isTotal`). The finite
elements are the principal filters `↑(Ici a)`. When `Δ` has no greatest element (e.g. `ℕ = ω`) the
total element is **not** finite (`topElement_not_principal_of_noMax`): not all elements are finite.

The system and `Ici` lemmas are `[propext, Quot.sound]`; the classification's surjectivity uses
the well-ordering (`WellFounded.has_min`), so it is classical. -/

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem



variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]




/-! ### Well-order: every neighbourhood is `Ici (its minimum)`. -/

variable [WellFoundedLT Δ]


/-! ### The classification of `|𝒟|` as the non-empty lower sets (initial segments). -/








/-! ### Total elements and finiteness (Scott's prose questions). -/

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
