/-ai
The two-injection of an element contains the two-copy of a neighbourhood Z exactly when the element contains Z.

If the copy belongs to the injection, it is not the master, because the master contains the point none and a two-copy does not. It is therefore a two-copy of some set, and injectivity of two-copies forces that set to be Z. Conversely, the two-copy of Z is one of the neighbourhoods recorded by the injection.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1

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

@[simp] theorem sinj2_mem_j2 {x₂ : V₂.Element} {Z : Set γ} (hZ : V₂.mem Z) :
    (sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₂).mem (j2 Z) ↔ x₂.mem Z := by
  constructor
  · rintro (h0 | ⟨Z', hZ', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
    · rw [j2_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Z, hZ, rfl, hx⟩

end SumInj

end DomainTheory.NeighbourhoodSystems
