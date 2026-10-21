/-ai
The union of down-sets of a cons list is the down-set of the head neighbourhood, united with the union of down-sets of the tail.

By extensionality and the membership law for the union, a witnessing code in the cons list is either the head or a member of the tail, and conversely a member of either summand supplies a code in the cons list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.mem_UPX

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem UPX_cons (b : ℕ) (l : List ℕ) :
    V.UPX P (b :: l) = V.upSet (P.X b) ∪ V.UPX P l := by
  ext z
  rw [Set.mem_union, V.mem_UPX P, V.mem_UPX P]
  constructor
  · rintro ⟨c, hc, hz⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact Or.inl hz
    · exact Or.inr ⟨c, hc', hz⟩
  · rintro (hz | ⟨c, hc, hz⟩)
    · exact ⟨b, List.mem_cons.mpr (Or.inl rfl), hz⟩
    · exact ⟨c, List.mem_cons.mpr (Or.inr hc), hz⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
