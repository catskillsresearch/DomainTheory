/-ai
A finite sequence of neighbourhoods is consistent if and only if some filter lies in the bracket of every term.

Consistency is rewritten as nonemptiness of the bracket of the finite intersection. An element of that bracket lies in each term's bracket by upward closure along the containment of the intersection in the term. Conversely, a filter that lies in every bracket contains every term, and therefore contains their finite intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.consistent_iff_bracket_interUpTo_nonempty

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)





/-- **Exercise 1.21 — consistency `⟺ ⋂_{i<n} [Xᵢ] ≠ ∅`.** The literal form of Scott's
equivalence: `⟨Xᵢ⟩` is consistent iff there is a filter lying in every `[Xᵢ]` (`i < n`). `→`
uses upward closure along `⋂_{i<n} Xᵢ ⊆ Xᵢ`; `←` uses `Element.mem_interUpTo`. -/
theorem consistent_iff_iInter_bracket_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ ∃ x : V.Element, ∀ i, i < n → x ∈ V.bracket (X i) := by
  rw [V.consistent_iff_bracket_interUpTo_nonempty X hX]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun i hi => x.up_mem hx (hX i hi) (V.interUpTo_subset X hi)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, x.mem_interUpTo X (fun i hi => hx i hi)⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
