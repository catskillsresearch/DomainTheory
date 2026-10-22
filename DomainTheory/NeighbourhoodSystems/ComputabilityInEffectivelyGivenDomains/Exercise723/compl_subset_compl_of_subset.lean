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

/-- **Choice-free antitone `compl`** (only the direction needed here): unlike the general
`Set.compl_subset_compl` (a `BooleanAlgebra` lemma whose `↔` proof is classical), this direction is
constructive contraposition and needs no excluded middle. -/
theorem compl_subset_compl_of_subset {X Y : Set ℕ} (h : X ⊆ Y) : Yᶜ ⊆ Xᶜ :=
  fun _ hx hxX => hx (h hxX)

end DomainTheory.NeighbourhoodSystems.Exercise723
