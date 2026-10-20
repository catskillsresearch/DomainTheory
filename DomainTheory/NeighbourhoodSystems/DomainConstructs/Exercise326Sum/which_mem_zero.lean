module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
















/-- `which(x)` selects `true` (`{0} ∈ which x`) exactly when `x` reaches into the left copy. -/
theorem which_mem_zero {x : (sum V₀ V₁ h₀ h₁).Element} :
    ((whichMap V₀ V₁ h₀ h₁).toElementMap x).mem Example12.zero
      ↔ ∃ X, V₀.mem X ∧ x.mem (inj₀ X) := by
  constructor
  · rintro ⟨W, hWx, _, _, hg⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, _⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
    · exact ⟨X, hX, hWx⟩
    · rcases hc with h | h
      · exact absurd h zero_ne_master
      · exact absurd h zero_ne_one
    · exact absurd hc zero_ne_master
  · rintro ⟨X, hX, hWx⟩
    exact ⟨inj₀ X, hWx, Or.inr (Or.inl ⟨X, hX, rfl⟩), Example12.mem_zero,
      Or.inl ⟨⟨X, hX, rfl⟩, Or.inr rfl⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise326
