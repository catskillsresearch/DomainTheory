module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

open scoped Classical in
/-- **Smash enumeration.** Index `t ↦` the proper product `prodNbhd X⁰_{t.1} X¹_{t.2}` when both
factors are proper, otherwise the master. The classical `if` (deciding `Xₙ = Δ₀`) is the *only*
classical input of the smash presentation. -/
noncomputable def smashEnum (t : ℕ) : Set (α ⊕ β) :=
  if P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master then
    prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2)
  else prodNbhd V₀.master V₁.master

end Smash

end DomainTheory.NeighbourhoodSystems
