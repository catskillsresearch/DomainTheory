/-ai
The packed consistency step applies the consistency update to the state in the inner first half of the second projection and the entry in the first projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.consUpd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

section ConsFold

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- `foldCode`-shaped wrapper of `consUpd` (state lives in `w.unpair.2.unpair.1`, entry in
`w.unpair.1`). -/
def consStp (projFn fc : ℕ → ℕ) (w : ℕ) : ℕ :=
  consUpd P projFn fc w.unpair.2.unpair.1 w.unpair.1

end ConsFold

end DomainTheory.NeighbourhoodSystems
