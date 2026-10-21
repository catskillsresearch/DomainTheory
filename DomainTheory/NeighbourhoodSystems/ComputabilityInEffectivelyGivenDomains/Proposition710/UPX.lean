/-ai
The union of down-sets indexed by a finite list of codes is the union, over the codes in the list, of the down-set of the neighbourhood named by that code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- The finite union of down-sets indexed by a `List` of `𝒟`-indices: `⋃_{b ∈ l} ↓X_b`. -/
def UPX (l : List ℕ) : Set (Set α) := ⋃ b ∈ l, V.upSet (P.X b)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
