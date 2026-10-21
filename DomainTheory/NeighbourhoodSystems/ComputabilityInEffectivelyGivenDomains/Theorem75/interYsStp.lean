/-ai
One step of the conditional output-intersection fold reads a packed state whose first component is the current entry and whose second component pairs the running codomain index with the input index. It intersects the running index with the entry's output index when the inclusion characteristic of the input index against the entry's input index equals 1, and otherwise returns the running index.
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

/-- One step of the `interYs`-index fold. State `pair entry (pair acc k)`: entry `e = w.unpair.1`,
running `𝒟₁`-index `acc = w.unpair.2.unpair.1`, input index `k = w.unpair.2.unpair.2` (the
`foldCode` parameter). Intersects `acc` with `e`'s output index when the inclusion test fires. -/
def interYsStp (incl0 : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn (isOne (incl0 (Nat.pair w.unpair.2.unpair.2 w.unpair.1.unpair.1)))
    (P₁.inter w.unpair.2.unpair.1 w.unpair.1.unpair.2) w.unpair.2.unpair.1

end DomainTheory.NeighbourhoodSystems
