/-ai
The relation that every index in the decoded list of c lies below some index in the decoded list of k is recursively decidable.

Swap the computable inclusion relation and close it under bounded existence over a decoded list, deciding existence of a lower index. Swap again and close under bounded universality over a decoded list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- `∀ a ∈ dl c, ∃ b ∈ dl k, X_a ⊆ X_b` is recursively decidable (nested bounded `∀/∃` over
`P.incl_computable`). -/
theorem subCode_computable :
    RecDecidable₂ (fun c k => ∀ a ∈ decodeList c, ∃ b ∈ decodeList k, P.X a ⊆ P.X b) := by
  have hinner : RecDecidable₂ (fun k a => ∃ b ∈ decodeList k, P.X a ⊆ P.X b) :=
    P.incl_computable.swap.bExistsList
  exact hinner.swap.bForallList

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
