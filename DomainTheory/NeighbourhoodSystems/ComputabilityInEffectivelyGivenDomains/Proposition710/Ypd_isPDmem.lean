module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.mem_Ypd

@[expose] public section

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
