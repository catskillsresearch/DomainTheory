/-ai
GraphIdx is antitone in the set of maps: if W' is contained in W, then GraphIdx W is contained in GraphIdx W'. Shrinking the set of maps can only add guaranteed content.

A code witnessed by n, m₀, and m for the larger set is witnessed by the same data for the smaller set, because the universal quantifier over maps is restricted along the inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.GraphIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- **`GraphIdx` is antitone: shrinking `W` (more information about the map) can only add
guaranteed content.** -/
theorem GraphIdx_mono {W W' : Set (ApproximableMap PN PN)} (h : W' ⊆ W) :
    GraphIdx W ⊆ GraphIdx W' := by
  rintro c ⟨n, m₀, m, rfl, hf, hbit⟩
  exact ⟨n, m₀, m, rfl, fun f hf' => hf f (h hf'), hbit⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
