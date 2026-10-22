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
