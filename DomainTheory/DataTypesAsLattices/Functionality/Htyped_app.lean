/-ai
Applying the typed interpretation of a term to an element yields the lambda retract of the interpretation of the term at the environment retract of that element.

Unfold the typed interpretation and the application equation for the arrow retract, simplify composition, and apply congruence of the lambda retract. The remaining equality is beta reduction by continuity of the interpretation at the retracted environment.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem Htyped_app (τ : LambTerm) (t : Pomega) :
    funOf (Htyped τ) t = funOf lambR (Hinterp τ (funOf envR t)) := by
  rw [Htyped, arrowR_app]
  simp only [comp_app]
  apply congrArg (funOf lambR)
  exact beta (Hinterp_isScottContinuous τ) (funOf envR t)

end DomainTheory.DataTypesAsLattices
