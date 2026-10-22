module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.10.** `h(x) = f(x) ∩ g(x)` (the meet in `|𝒟₁|`). The non-trivial direction combines
witnesses `X ∈ x` (for `f`) and `X' ∈ x` (for `g`) through `X ∩ X' ∈ x` using `mono`. -/
theorem mem_toElementMap_interMap (f g : ApproximableMap V₀ V₁) (x : V₀.Element) {Z : Set β} :
    ((interMap f g).toElementMap x).mem Z ↔
      (f.toElementMap x).mem Z ∧ (g.toElementMap x).mem Z := by
  constructor
  · rintro ⟨X, hxX, hf, hg⟩
    exact ⟨⟨X, hxX, hf⟩, ⟨X, hxX, hg⟩⟩
  · rintro ⟨⟨X, hxX, hf⟩, ⟨X', hxX', hg⟩⟩
    have hxXX' : x.mem (X ∩ X') := x.inter_mem hxX hxX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hxXX'
    refine ⟨X ∩ X', hxXX', ?_, ?_⟩
    · exact f.mono hf Set.inter_subset_left subset_rfl hXX' (f.rel_cod hf)
    · exact g.mono hg Set.inter_subset_right subset_rfl hXX' (g.rel_cod hg)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
