/-ai
On a left element of a separated sum, one that meets some left copy, the left injection after the left projection is the identity.

If an output belongs to the round trip, an intermediate left neighbourhood comes from a sum neighbourhood of the element whose left content sits in that intermediate set, and the left copy of the intermediate set sits in the output. Intersecting with the given left copy produces a smaller left copy inside the output, so the output belongs to the element. Conversely, a neighbourhood of the element is the sum master, a left copy, or a right copy. The master is reached from the left master through the sum master, a left copy is reached from itself, and a right copy meets the given left copy in the empty set, which is not a sum neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.not_sum_mem_empty

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
















/-- On a "left" element (one reaching into the left copy), the round-trip `in₀ ∘ out₀` is the
identity. -/
theorem inMap₀_outMap₀_eq_of_left {x : (sum V₀ V₁ h₀ h₁).Element}
    (hL : ∃ X, V₀.mem X ∧ x.mem (inj₀ X)) :
    (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap ((outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x) = x := by
  obtain ⟨X₀, hX₀, hxX₀⟩ := hL
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, ⟨W, hxW, _, _, hLWX⟩, _, hSZ, hinjXZ⟩
    -- W ∩ inj₀ X₀ is a left copy inj₀ X₁ ⊆ Z, and lies in x
    have hxWX₀ : x.mem (W ∩ inj₀ X₀) := x.inter_mem hxW hxX₀
    obtain ⟨X₁, _, hX₁eq⟩ := mem_subset_inj₀ (x.sub hxWX₀) Set.inter_subset_right
    have hX₁X : X₁ ⊆ X := by
      have : leftPart V₀ (W ∩ inj₀ X₀) ⊆ X :=
        (leftPart_mono V₀ Set.inter_subset_left).trans hLWX
      rwa [hX₁eq, leftPart_inj₀] at this
    have : (W ∩ inj₀ X₀) ⊆ Z :=
      hX₁eq ▸ (inj₀_subset_inj₀.mpr hX₁X).trans hinjXZ
    exact x.up_mem hxWX₀ hSZ this
  · intro hxZ
    rcases x.sub hxZ with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · -- Z = sumMaster
      exact ⟨V₀.master, ⟨sumMaster V₀ V₁, x.master_mem, (sum V₀ V₁ h₀ h₁).master_mem,
        V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩, V₀.master_mem,
        (sum V₀ V₁ h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
    · -- Z = inj₀ X'
      exact ⟨X', ⟨inj₀ X', hxZ, Or.inr (Or.inl ⟨X', hX', rfl⟩), hX', (leftPart_inj₀ V₀ X').subset⟩,
        hX', Or.inr (Or.inl ⟨X', hX', rfl⟩), subset_rfl⟩
    · -- Z = inj₁ Y' is impossible for a left element
      have := x.inter_mem hxX₀ hxZ
      rw [inj₀_inter_inj₁] at this
      exact absurd (x.sub this) not_sum_mem_empty

end DomainTheory.NeighbourhoodSystems.Exercise326
