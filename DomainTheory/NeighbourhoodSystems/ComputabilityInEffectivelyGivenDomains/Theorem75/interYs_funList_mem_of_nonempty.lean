/-ai
If the step-function neighbourhood of a presented list is nonempty, then for every domain neighbourhood the conditional output intersection of that list against the neighbourhood is a codomain neighbourhood.

Name the domain neighbourhood by a presentation index and take a map in the step-function neighbourhood. That map relates the named neighbourhood to the conditional output intersection, so the intersection is a codomain neighbourhood as the codomain of a relation of the map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.rel_interYs_funList

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- If `stepFun (funListOf ea)` is non-empty, then `interYs Δ₁ (funListOf ea) X` is a neighbourhood of
`𝒟₁` for every `X ∈ 𝒟₀` (the consistency hypothesis needed by `leastMap`). Choice-free. -/
theorem interYs_funList_mem_of_nonempty {ea : List ℕ}
    (h : (stepFun (funListOf P₀ P₁ ea) : Set (ApproximableMap V₀ V₁)).Nonempty)
    {X : Set α} (hX : V₀.mem X) :
    V₁.mem (interYs V₁.master (funListOf P₀ P₁ ea) X) := by
  obtain ⟨n', hn'⟩ := P₀.surj hX
  obtain ⟨f, hf⟩ := h
  have hr := rel_interYs_funList P₀ P₁ hf n'
  rw [hn'] at hr
  exact f.rel_cod hr

end DomainTheory.NeighbourhoodSystems
