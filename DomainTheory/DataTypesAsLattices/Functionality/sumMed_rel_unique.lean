/-ai
Coproduct mediators are unique up to the codomain restricted equivalence. If h lies in the function space from the sum of A and B to C, and h agrees with f on left injections and with g on right injections in the sense of C, then h is related to the mediator of f and g in the function space from that sum to C.

The two graph equations are the given membership of h and the graph law for the mediator. On a related pair in the sum, each application is rewritten along the common tag, and the left or right agreement hypothesis supplies the relation in C.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app_inl
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app_inr
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- Coproduct mediators are unique up to the codomain restricted
equivalence, which is categorical arrow equality in this presentation. -/
theorem sumMed_rel_unique {A B C : RestrictedEquiv} {f g h : Pomega}
    (hh : (arrowE (sumE A B) C).mem h)
    (hinl : ∀ x y, A.rel x y →
      C.rel (funOf h (pairElem (ofNat 0) x)) (funOf f y))
    (hinr : ∀ x y, B.rel x y →
      C.rel (funOf h (pairElem (ofNat 1) x)) (funOf g y)) :
    (arrowE (sumE A B) C).rel h (sumMed f g) := by
  refine ⟨hh.1, sumMed_isGraph f g, ?_⟩
  intro u v huv
  rcases huv with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
  · have hhu :
        funOf h u = funOf h (pairElem (ofNat 0) (funOf u (ofNat 1))) :=
      congrArg (fun w => funOf h w) hu
    have hmv : funOf (sumMed f g) v = funOf f (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed_app_inl f g _)
    rw [hhu, hmv]
    exact hinl (funOf u (ofNat 1)) (funOf v (ofNat 1)) hA
  · have hhu :
        funOf h u = funOf h (pairElem (ofNat 1) (funOf u (ofNat 1))) :=
      congrArg (fun w => funOf h w) hu
    have hmv : funOf (sumMed f g) v = funOf g (funOf v (ofNat 1)) :=
      (congrArg (fun w => funOf (sumMed f g) w) hv).trans
        (sumMed_app_inr f g _)
    rw [hhu, hmv]
    exact hinr (funOf u (ofNat 1)) (funOf v (ofNat 1)) hB

end DomainTheory.DataTypesAsLattices
