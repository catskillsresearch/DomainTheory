/-ai
One step of the triviality fold returns 0 when the running flag is off, and otherwise returns the bit that the equality characteristic assigns to the current entry's output index paired with the master index.
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

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- One step of the trivial-test fold: is this entry's output index equal to `masterIdx`? -/
def trivStp (eq1 : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn w.unpair.2.unpair.1
    (isOne (eq1 (Nat.pair w.unpair.1.unpair.2 P₁.masterIdx))) 0

end DomainTheory.NeighbourhoodSystems
