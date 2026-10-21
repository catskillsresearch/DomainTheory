/-ai
If a binary operation is Scott-continuous in each argument separately, and two maps are Scott-continuous, then the operation along those two maps is Scott-continuous.

Diagonal continuity applies. The first factor is Theorem 1.3 of continuity in the first argument with continuity of the first map, and the second factor is Theorem 1.3 of continuity in the second argument with continuity of the second map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_on_diag

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














theorem continuous_tuple {F : Pomega → Pomega → Pomega}
    (h1 : ∀ y, IsScottContinuous (fun x => F x y))
    (h2 : ∀ x, IsScottContinuous (fun y => F x y))
    {g h : Pomega → Pomega} (hg : IsScottContinuous g) (hh : IsScottContinuous h) :
    IsScottContinuous (fun x => F (g x) (h x)) :=
  continuous_on_diag
    (fun v => theorem_1_3 (h1 (h v)) hg)
    (fun u => theorem_1_3 (h2 (g u)) hh)

end DomainTheory.DataTypesAsLattices
