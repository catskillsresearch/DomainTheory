/-ai
The list lookup of a code c at an index i is the second component of the fold, over c, of the indexing step, started from the pair of i plus one and zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGetStp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `listGet c i = (decodeList c).getD i 0`: the `i`-th entry of the list coded by `c`. -/
def listGet (c i : ℕ) : ℕ :=
  (foldCode listGetStp 0 (Nat.pair (i + 1) 0) c).unpair.2

end Proposition77

end DomainTheory.NeighbourhoodSystems
