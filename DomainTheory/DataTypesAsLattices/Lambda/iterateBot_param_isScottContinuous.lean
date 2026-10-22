module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem iterateBot_param_isScottContinuous
    {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) :
    ∀ n, IsScottContinuous (fun x => iterateBot (g x) n)
  | 0 => const_isScottContinuous botElem
  | n + 1 =>
    theorem_1_3_tuple (hgx) (hgy) id_isScottContinuous
      (iterateBot_param_isScottContinuous hgx hgy n)

end DomainTheory.DataTypesAsLattices
