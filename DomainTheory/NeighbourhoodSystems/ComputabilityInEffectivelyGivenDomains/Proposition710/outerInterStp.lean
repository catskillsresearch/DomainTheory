module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.innerInterCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- One step of the **outer** fold (over `decodeList n`, parameter `m`): run the inner fold for the
current outer index `a`. `foldCode` shape: state `w = ⟨a, ⟨acc, m⟩⟩`. -/
def outerInterStp (cons : ℕ → ℕ) (w : ℕ) : ℕ :=
  V.innerInterCode P cons w.unpair.1 w.unpair.2.unpair.1 w.unpair.2.unpair.2

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
