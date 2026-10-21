/-ai
Tag of a list at a value equals the right fold of the list of the map sending an entry and an accumulator to the numeral of the successor of the entry and the accumulator, starting from the numeral of zero and the value. The recursion of tag is this right fold.

The proof is induction on the list. The empty list is reflexive. At a cons cell, the cons equation for tag and the inductive hypothesis leave a reflexive equality.
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


/-- **`tag` reformulated as a left fold over the reversed list.** `tag`'s recursion is a `foldr`;
`List.foldl_reverse` bridges it to the `foldl`-shaped `foldCode`. -/
theorem tag_eq_foldr (ns : List ℕ) (m : ℕ) :
    tag ns m = ns.foldr (fun x y => num (x + 1) y) (num 0 m) := by
  induction ns with
  | nil => rfl
  | cons a ns ih => rw [tag_cons, ih]; rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
