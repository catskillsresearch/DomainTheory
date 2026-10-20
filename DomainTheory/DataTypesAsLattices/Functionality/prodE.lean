module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (7.7).** Product of restricted equivalences. -/
def prodE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun u v =>
    u = pairElem (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
      v = pairElem (funOf v (ofNat 0)) (funOf v (ofNat 1)) ∧
        A.rel (funOf u (ofNat 0)) (funOf v (ofNat 0)) ∧
          B.rel (funOf u (ofNat 1)) (funOf v (ofNat 1))
  symm := by
    intro u v ⟨hu, hv, h0, h1⟩
    exact ⟨hv, hu, A.symm h0, B.symm h1⟩
  trans := by
    intro u v w ⟨hu, hv, h0, h1⟩ ⟨hv', hw, k0, k1⟩
    exact ⟨hu, hw, A.trans h0 k0, B.trans h1 k1⟩

end DomainTheory.DataTypesAsLattices
