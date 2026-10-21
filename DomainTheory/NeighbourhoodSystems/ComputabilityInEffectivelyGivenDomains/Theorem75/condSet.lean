/-ai
The conditional set of a base along an entry list, relative to a domain index, is the set of points of the base that lie in each output whose input contains the neighbourhood at that index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- The running set of the conditional `inter`-chain: `A` intersected with the outputs `X₁_{e.2}` of
the entries `e ∈ el` whose input dominates `X₀_k`. -/
def condSet (k : ℕ) (A : Set β) (el : List ℕ) : Set β :=
  {z | z ∈ A ∧ ∀ e ∈ el, P₀.X k ⊆ P₀.X e.unpair.1 → z ∈ P₁.X e.unpair.2}

end DomainTheory.NeighbourhoodSystems
