module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PDmem_inter

@[expose] public section

set_option linter.unusedSectionVars false

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
