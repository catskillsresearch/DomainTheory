module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Each product term `↓X ∩ ↓Y` is a `ℙ𝒟`-neighbourhood.** By `upSet_inter` it is `↓(X ∩ Y)`; if
`{X, Y}` is consistent (`X ∩ Y ∈ 𝒟`) this is the down-set of a neighbourhood (`PDmem_upSet`),
otherwise `↓(X ∩ Y) = ∅` (no `Z ∈ 𝒟` lies below `X ∩ Y`), the empty union (`PDmem_empty`). The
`by_cases` on `V.mem (X ∩ Y)` is the lone `Classical` step (deciding membership in an arbitrary
system). -/
theorem PDmem_upSet_inter {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.PDmem (V.upSet X ∩ V.upSet Y) := by
  rw [V.upSet_inter]
  by_cases h : V.mem (X ∩ Y)
  · exact V.PDmem_upSet h
  · have hempty : V.upSet (X ∩ Y) = ∅ := by
      ext Z
      simp only [mem_upSet, Set.mem_empty_iff_false, iff_false, not_and]
      intro hZmem hZsub
      exact h (V.inter_mem hX hY hZmem hZsub)
    rw [hempty]; exact V.PDmem_empty

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
