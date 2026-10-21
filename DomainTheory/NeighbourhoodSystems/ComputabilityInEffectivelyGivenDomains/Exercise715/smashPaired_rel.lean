/-ai
The strict pairing relates Z to W exactly when both are neighbourhoods and either W is the product of the two masters or W is a proper product whose factors are related to Z by the two maps.

The two sides are the same proposition by definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

@[simp] theorem smashPaired_rel {V₂ : NeighborhoodSystem γ} {a : ApproximableMap V₂ V₀}
    {b : ApproximableMap V₂ V₁} {Z : Set γ} {W : Set (α ⊕ β)} :
    (smashPaired a b).rel Z W ↔ V₂.mem Z ∧ (smash V₀ V₁).mem W ∧
      (W = prodNbhd V₀.master V₁.master ∨
        ∃ A B, W = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧ a.rel Z A ∧ b.rel Z B) :=
  Iff.rfl

end Smash

end DomainTheory.NeighbourhoodSystems
