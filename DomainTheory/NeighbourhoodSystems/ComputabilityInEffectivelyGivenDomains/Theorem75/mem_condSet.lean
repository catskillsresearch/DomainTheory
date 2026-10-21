/-ai
A point lies in the conditional set of a base along a code list, relative to an input index, if and only if it lies in the base and, for every code in the list, lies in the corresponding output neighbourhood whenever the neighbourhood at the input index is contained in that code's input neighbourhood.

This is reflexivity of the defining equivalence of the conditional set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem mem_condSet {k : ℕ} {A : Set β} {el : List ℕ} {z : β} :
    z ∈ condSet P₀ P₁ k A el ↔ z ∈ A ∧ ∀ e ∈ el, P₀.X k ⊆ P₀.X e.unpair.1 → z ∈ P₁.X e.unpair.2 :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems
