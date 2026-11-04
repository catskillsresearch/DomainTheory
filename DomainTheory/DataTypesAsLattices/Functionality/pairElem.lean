module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def pairElem (x y : Pomega) : Pomega := seq2 x y

namespace pairElem

theorem tag_ne (x y : Pomega) :
    pairElem (ofNat 0) x ≠ pairElem (ofNat 1) y :=
  seq2.tag_ne x y

theorem eq_pairSeq (x y : Pomega) : pairElem x y = pairSeq x y := rfl

theorem fst (x y : Pomega) : funOf (pairElem x y) (ofNat 0) = x :=
  seq2.zero x y

theorem snd (x y : Pomega) : funOf (pairElem x y) (ofNat 1) = y :=
  seq2.one x y

theorem inj {x y x' y' : Pomega} (h : pairElem x y = pairElem x' y') :
    x = x' ∧ y = y' := by
  constructor
  · have := congrArg (fun w => funOf w (ofNat 0)) h
    rw [fst, fst] at this
    exact this
  · have := congrArg (fun w => funOf w (ofNat 1)) h
    rw [snd, snd] at this
    exact this

end pairElem

end DomainTheory.DataTypesAsLattices
