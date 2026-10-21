/-ai
The complement of the intersection of nbhd a and nbhd b equals the union of the two complements. Membership in these neighbourhoods is decided by test bits, so the identity does not need a general excluded middle.

Extend the two sets in the point and simplify membership. Case-splitting on the bit of a and the bit of b, decide closes every Boolean combination.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- **Choice-free De Morgan for `nbhd`'s excluded sets.** The general `Set.compl_inter` needs
excluded middle; here, since membership in `nbhd a`/`nbhd b` is decided by `Nat.testBit`, a case
split on the two (concrete) bits suffices. -/
theorem compl_inter_nbhd (a b : ℕ) : (nbhd a ∩ nbhd b)ᶜ = (nbhd a)ᶜ ∪ (nbhd b)ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, mem_nbhd]
  cases a.testBit x <;> cases b.testBit x <;> decide

end DomainTheory.NeighbourhoodSystems.Exercise723
