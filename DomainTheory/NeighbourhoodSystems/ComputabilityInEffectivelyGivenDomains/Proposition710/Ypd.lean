module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- **The enumeration of `ℙ𝒟`.** `Ypd c = ⋃_{a ∈ decodeList c} ↓X_a` — a finite union of down-sets,
ranging over all of `ℙ𝒟` as `c` ranges over `ℕ` (the empty code `0` gives `∅`). -/
def Ypd (c : ℕ) : Set (Set α) := V.UPX P (decodeList c)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
