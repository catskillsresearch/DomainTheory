module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

@[simp] theorem sinj1_mem_j1 {x₁ : V₁.Element} {Y : Set β} (hY : V₁.mem Y) :
    (sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₁).mem (j1 Y) ↔ x₁.mem Y := by
  constructor
  · rintro (h0 | ⟨Y', hY', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · rw [j1_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Y, hY, rfl, hx⟩

end SumInj

end DomainTheory.NeighbourhoodSystems
