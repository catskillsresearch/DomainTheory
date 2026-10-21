/-ai
The set elemSet x is the subset of the natural numbers positively described by an element x of PN. It consists of those k for which some neighbourhood nbhd n contained in x has its k-th bit set, equivalently the union of the finite sets excluded by the neighbourhoods that x contains.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- The subset of `ℕ` "positively described" by a `PN`-element `x`: the union of the excluded finite
sets of every neighbourhood it contains. -/
def elemSet (x : PN.Element) : Set ℕ := {k | ∃ n, x.mem (nbhd n) ∧ n.testBit k = true}

end DomainTheory.NeighbourhoodSystems.Exercise723
