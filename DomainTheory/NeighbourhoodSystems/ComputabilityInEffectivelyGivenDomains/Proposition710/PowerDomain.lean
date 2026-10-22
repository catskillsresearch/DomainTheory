/-ai
The Smyth power domain is the neighbourhood system on sets whose neighbourhoods are the power-domain neighbourhoods and whose master neighbourhood is the down-set of the master. That down-set contains the master, hence is nonempty, and is itself a power-domain neighbourhood. Binary intersection of neighbourhoods stays in the family. Every power-domain neighbourhood is contained in the down-set of the master, because each set in a finite union of down-sets lies in the down-set of some neighbourhood, and that neighbourhood is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PDmem_inter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Proposition 7.10 (Part A) — the Smyth power domain `ℙ𝒟` as a neighbourhood system.** Master
`↓Δ`; closure under intersection is `PDmem_inter`; `↓X ⊆ ↓Δ` since `X ⊆ Δ`. -/
abbrev PowerDomain : NeighborhoodSystem (Set α) where
  mem := V.PDmem
  master := V.upSet V.master
  master_nonempty := ⟨V.master, V.master_mem, subset_rfl⟩
  master_mem := V.PDmem_master
  inter_mem := fun h₁ h₂ _ _ => V.PDmem_inter h₁ h₂
  sub_master := by
    intro W hW
    obtain ⟨L, hL, rfl⟩ := hW
    intro Z hZ
    rw [V.mem_PDunion] at hZ
    obtain ⟨X, hX, hZmem, hZsub⟩ := hZ
    exact ⟨hZmem, hZsub.trans (V.sub_master (hL X hX))⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
