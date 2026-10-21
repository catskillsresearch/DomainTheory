/-ai
The intersection of the down-sets of two neighbourhoods is a power-domain neighbourhood. By the intersection law for down-sets it is the down-set of the intersection. If that intersection is a neighbourhood, the result is the down-set of a neighbourhood; otherwise the down-set is empty, since no neighbourhood lies below the intersection. The case split on membership of the intersection is the classical step.

Rewrite by the down-set intersection law. If the intersection is a neighbourhood, its down-set is a power-domain neighbourhood. If it is not, the down-set is empty, because a neighbourhood contained in the intersection would witness membership of the intersection by closure under intersection, and the empty set is a power-domain neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

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
