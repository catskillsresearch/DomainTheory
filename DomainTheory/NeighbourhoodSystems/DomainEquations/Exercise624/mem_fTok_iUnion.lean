module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_gTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_fTok

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624





/-- **Additivity of `fTok`.** Every token of `fTok (⋃ₙ aₙ) (⋃ₙ bₙ)` already lies in some
`fTok aₙ bₙ`. The nested `true`-branch (the product copy `0p` inside `1(gTok p q)`) still references
at most one coordinate, so a single finite stage suffices. -/
theorem mem_fTok_iUnion {a b : ℕ → Set Str} {w : Str}
    (hw : w ∈ fTok (⋃ n, a n) (⋃ n, b n)) : ∃ n, w ∈ fTok (a n) (b n) := by
  rcases hw with rfl | ⟨w', rfl, hw'⟩ | ⟨u, rfl, hu⟩
  · exact ⟨0, nil_mem_fTok _ _⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inl ⟨w', rfl, hn⟩)⟩
  · rcases hu with rfl | ⟨u', rfl, hu'⟩ | ⟨u', rfl, hu'⟩
    · exact ⟨0, Or.inr (Or.inr ⟨[], rfl, nil_mem_gTok _ _⟩)⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu'
      exact ⟨n, Or.inr (Or.inr ⟨false :: u', rfl, Or.inr (Or.inl ⟨u', rfl, hn⟩)⟩)⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu'
      exact ⟨n, Or.inr (Or.inr ⟨true :: u', rfl, Or.inr (Or.inr ⟨u', rfl, hn⟩)⟩)⟩

end Exercise624
end DomainTheory.NeighbourhoodSystems
