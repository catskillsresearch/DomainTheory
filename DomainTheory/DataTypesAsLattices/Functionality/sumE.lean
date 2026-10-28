
module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def sumE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun u v =>
    (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
        v = pairElem (ofNat 0) (funOf v (ofNat 1)) ∧
        A.rel (funOf u (ofNat 1)) (funOf v (ofNat 1))) ∨
      (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
        v = pairElem (ofNat 1) (funOf v (ofNat 1)) ∧
        B.rel (funOf u (ofNat 1)) (funOf v (ofNat 1)))
  symm := by
    intro u v h
    rcases h with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
    · exact Or.inl ⟨hv, hu, A.symm hA⟩
    · exact Or.inr ⟨hv, hu, B.symm hB⟩
  trans := by
    intro u v w h1 h2
    rcases h1 with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
    · rcases h2 with ⟨hv', hw, hA'⟩ | ⟨hv', hw, _⟩
      · exact Or.inl ⟨hu, hw, A.trans hA hA'⟩
      · exact (pairElem.tag_ne (funOf v (ofNat 1)) (funOf v (ofNat 1))
          (hv.symm.trans hv')).elim
    · rcases h2 with ⟨hv', hw, _⟩ | ⟨hv', hw, hB'⟩
      · exact (pairElem.tag_ne (funOf v (ofNat 1)) (funOf v (ofNat 1))
          (hv'.symm.trans hv)).elim
      · exact Or.inr ⟨hu, hw, B.trans hB hB'⟩

end DomainTheory.DataTypesAsLattices
