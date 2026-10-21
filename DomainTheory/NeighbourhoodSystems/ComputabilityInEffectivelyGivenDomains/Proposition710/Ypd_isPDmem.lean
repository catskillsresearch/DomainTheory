/-ai
Every coded neighbourhood is a power-domain neighbourhood, witnessed by the list of enumerated neighbourhoods of the codes in its decoded list.

Each entry of that list is an enumerated neighbourhood, hence a neighbourhood of the original system. A set lies in the coded neighbourhood exactly when it lies in the down-set of some decoded code, and it lies in the power-domain union of the list exactly when it lies in the down-set of the enumerated neighbourhood of such a code. The two descriptions match by sending each code to its enumerated neighbourhood and back.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.mem_Ypd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- Every `Ypd c` is a `ℙ𝒟`-neighbourhood (list `(decodeList c).map P.X`). -/
theorem Ypd_isPDmem (c : ℕ) : V.PDmem (V.Ypd P c) := by
  refine ⟨(decodeList c).map P.X, ?_, ?_⟩
  · intro X hX
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hX
    exact P.mem_X a
  · ext z
    rw [V.mem_Ypd P, V.mem_PDunion]
    constructor
    · rintro ⟨a, ha, hz⟩; exact ⟨P.X a, List.mem_map.mpr ⟨a, ha, rfl⟩, hz⟩
    · rintro ⟨X, hX, hz⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hX
      exact ⟨a, ha, hz⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
