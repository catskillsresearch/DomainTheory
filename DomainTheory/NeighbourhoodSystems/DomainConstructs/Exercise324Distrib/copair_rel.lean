/-ai
The copairing relates a sum neighbourhood to an output neighbourhood exactly when the output is the master, or the input is a left copy related by the first map, or the input is a right copy related by the second map.

The two sides are the defining relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

@[simp] theorem copair_rel {a : ApproximableMap V₀ V₂} {b : ApproximableMap V₁ V₂}
    {W : Set (Option (α ⊕ β))} {Z : Set γ} :
    (copair (h₀ := h₀) (h₁ := h₁) a b).rel W Z ↔ (sum V₀ V₁ h₀ h₁).mem W ∧ V₂.mem Z ∧
      (Z = V₂.master ∨ (∃ X, W = inj₀ X ∧ a.rel X Z) ∨ (∃ Y, W = inj₁ Y ∧ b.rel Y Z)) := Iff.rfl

end DomainTheory.NeighbourhoodSystems
