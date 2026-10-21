/-ai
If a binary operation is Scott continuous in each argument separately, then every bottom iterate of its first-argument slice is Scott continuous in that argument.

The zeroth iterate is the constant bottom element. The next iterate is the tuple form of Theorem 1.3 applied to continuity in each argument, continuity of the identity, and the inductive hypothesis.
ai-/
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
