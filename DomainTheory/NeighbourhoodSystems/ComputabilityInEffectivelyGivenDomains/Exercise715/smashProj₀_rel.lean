/-ai
The left smash projection relates W to X' exactly when both are neighbourhoods and the left preimage of W is contained in X'.

The two sides are the same proposition by definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

@[simp] theorem smashProj₀_rel {W : Set (α ⊕ β)} {X' : Set α} :
    (smashProj₀ V₀ V₁).rel W X' ↔ (smash V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X' := Iff.rfl

end Smash

end DomainTheory.NeighbourhoodSystems
