
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


/-- **`tag` reformulated as a left fold over the reversed list.** `tag`'s recursion is a `foldr`;
`List.foldl_reverse` bridges it to the `foldl`-shaped `foldCode`. -/
theorem tag_eq_foldr (ns : List ℕ) (m : ℕ) :
    tag ns m = ns.foldr (fun x y => num (x + 1) y) (num 0 m) := by
  induction ns with
  | nil => rfl
  | cons a ns ih => rw [tag_cons, ih]; rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
