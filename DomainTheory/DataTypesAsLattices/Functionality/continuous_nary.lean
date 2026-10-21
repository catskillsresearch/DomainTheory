/-ai
If a ternary operation is Scott-continuous in each argument separately, and three maps are Scott-continuous, then the operation along those three maps is Scott-continuous.

Diagonal continuity applies. The first diagonal factor is the binary continuity package of the continuities in the first two arguments, along the first two maps. The second diagonal factor is Theorem 1.3 applied to continuity in the third argument and continuity of the third map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_on_diag
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem continuous_nary {F : Pomega → Pomega → Pomega → Pomega}
    (hf0 : ∀ y z, IsScottContinuous (fun x => F x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => F x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => F x y z))
    {g h i : Pomega → Pomega}
    (hg : IsScottContinuous g) (hh : IsScottContinuous h) (hi : IsScottContinuous i) :
    IsScottContinuous (fun x => F (g x) (h x) (i x)) :=
  continuous_on_diag
    (fun v => continuous_tuple (fun y => hf0 y (i v)) (fun x => hf1 x (i v)) hg hh)
    (fun u => theorem_1_3 (hf2 (g u) (h u)) hi)

end DomainTheory.DataTypesAsLattices
