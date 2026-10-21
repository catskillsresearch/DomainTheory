/-ai
On indices, graphMap relates the enumerated set of maps coded by c to the neighbourhood nbhd m if and only if the complement of nbhd m is contained in GraphIdx of that enumerated set. The decider gN is the nonempty test of the function-space presentation.

A related triple contains the inclusion. Conversely, the enumerated set is a neighbourhood by the enumeration lemma for gN, nbhd m is a neighbourhood, and the hypothesis is the inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- `graphMap`'s neighbourhood relation on indices: `Xenum … c` relates to `nbhd m` iff `nbhd m`'s
excluded set fits inside `GraphIdx (Xenum … c)`. -/
theorem graphMap_rel_iff (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf PNpres PNpres (decodeList c))
      : Set (ApproximableMap PN PN)).Nonempty) (c m : ℕ) :
    graphMap.rel (Xenum PNpres PNpres gN c) (nbhd m) ↔
      (nbhd m)ᶜ ⊆ GraphIdx (Xenum PNpres PNpres gN c) := by
  constructor
  · rintro ⟨_, _, hsub⟩; exact hsub
  · intro h; exact ⟨Xenum_mem PNpres PNpres gN hgN c, ⟨m, rfl⟩, h⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
