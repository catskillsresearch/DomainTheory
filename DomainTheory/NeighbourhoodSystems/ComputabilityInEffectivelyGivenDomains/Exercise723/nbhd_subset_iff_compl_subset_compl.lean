/-ai
The neighbourhood nbhd a is contained in nbhd b if and only if the complement of nbhd b is contained in the complement of nbhd a. Membership in these neighbourhoods is decided by a test bit, so the reverse direction needs only a Boolean case split.

The forward direction is antitonicity of complement. Conversely, take a point of nbhd a and rewrite membership. If the corresponding bit of b is false, the point lies in nbhd b by definition. If that bit is true, the point lies in the complement of nbhd b and hence in the complement of nbhd a, which contradicts the rewritten membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_compl_nbhd

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



























/-- **Choice-free converse of `compl_subset_compl_of_subset`, specialized to `nbhd`.** For cofinite
neighbourhoods the excluded sets have decidable membership (`Nat.testBit`), so unlike the general
`Set.compl_subset_compl` this direction needs only a case split on a `Bool`, not excluded middle. -/
theorem nbhd_subset_iff_compl_subset_compl (a b : ℕ) :
    nbhd a ⊆ nbhd b ↔ (nbhd b)ᶜ ⊆ (nbhd a)ᶜ := by
  constructor
  · exact compl_subset_compl_of_subset
  · intro h x hxa
    rw [mem_nbhd] at hxa ⊢
    cases hbit : b.testBit x with
    | false => rfl
    | true => exact absurd (mem_compl_nbhd.mp (h (mem_compl_nbhd.mpr hbit))) (by rw [hxa]; decide)

end DomainTheory.NeighbourhoodSystems.Exercise723
