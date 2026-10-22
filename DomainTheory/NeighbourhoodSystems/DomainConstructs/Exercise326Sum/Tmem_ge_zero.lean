module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- A `T`-neighbourhood containing `{0}` is `{0}` or `Δ`. -/
theorem Tmem_ge_zero {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.zero ⊆ C) : C = Example12.zero ∨ C = Example12.master := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])

end DomainTheory.NeighbourhoodSystems.Exercise326
