/-ai
The index of the conditional output intersection of the list decoded from a against the domain neighbourhood at k is the fold of the interYs step, with parameter k, starting from the codomain master index, over the list coded by a.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interYsStp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- The index of `interYs Δ₁ (funListOf (decodeList a)) (X₀_k)`: a conditional `inter`-fold over
`decodeList a` from `masterIdx`, with `k` carried as the `foldCode` parameter. -/
def interYsIdx (incl0 : ℕ → ℕ) (a k : ℕ) : ℕ :=
  foldCode (interYsStp P₁ incl0) k P₁.masterIdx a

end DomainTheory.NeighbourhoodSystems
