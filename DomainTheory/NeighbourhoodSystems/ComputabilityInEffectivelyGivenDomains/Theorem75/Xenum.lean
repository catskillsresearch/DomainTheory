/-ai
The function-space enumeration at a code is the step neighbourhood of the decoded entry list when the consistency character returns one, and the whole space of maps otherwise.
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

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- The function-space enumeration: a code `c` lists step-pairs; if they are consistent (`gN c = 1`,
where `gN` is the consistency char) the neighbourhood is `stepFun (funListOf (decodeList c))`,
otherwise we send the junk code to the master neighbourhood `univ`. Choice-free as *data* because the
branch is a `Nat`-equality `if`. -/
def Xenum (gN : ℕ → ℕ) (c : ℕ) : Set (ApproximableMap V₀ V₁) :=
  if gN c = 1 then stepFun (funListOf P₀ P₁ (decodeList c)) else Set.univ

end DomainTheory.NeighbourhoodSystems
