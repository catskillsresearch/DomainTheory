/-ai
The sum enumeration sends a code to the left copy of the first presentation's neighbourhood when the tag is zero, to the right copy of the second presentation's neighbourhood when the tag is one, and to the sum master otherwise.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation_X

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- Scott's `Z₀ = Δ, Z_{2n+1} = X⁰ₙ, Z_{2n+2} = X¹ₙ`, realized with a `Nat.pair` tag: `tag = 0 ↦ 0X⁰`,
`tag = 1 ↦ 1X¹`, else the master. -/
def sumEnum (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) (t : ℕ) :
    Set (Option (α ⊕ β)) :=
  if t.unpair.1 = 0 then inj₀ (P₀.X t.unpair.2)
  else if t.unpair.1 = 1 then inj₁ (P₁.X t.unpair.2)
  else sumMaster V₀ V₁

end Sum

end DomainTheory.NeighbourhoodSystems
