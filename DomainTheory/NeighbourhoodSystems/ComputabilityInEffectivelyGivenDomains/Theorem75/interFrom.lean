/-ai
The running intersection of a set A along a list of indices is A on the empty list, and on a cons it is the running intersection, along the tail, of A intersected with the neighbourhood at the head.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

section ConsChain

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- The running intersection of `A` with the neighbourhoods `X_j` (`j ∈ js`), left-accumulated to
match `List.foldl`. -/
def interFrom (A : Set α) : List ℕ → Set α
  | [] => A
  | j :: js => interFrom (A ∩ P.X j) js

end ConsChain

end DomainTheory.NeighbourhoodSystems
