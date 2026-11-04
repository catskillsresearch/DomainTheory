module

public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Retracts.envR
public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import DomainTheory.DataTypesAsLattices.Retracts.typed_more
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Htyped (τ : LambTerm) : Pomega :=
  funOf (arrowR envR lambR) (graph (Hinterp τ))

namespace Htyped

theorem app (τ : LambTerm) (t : Pomega) :
    funOf (Htyped τ) t = funOf lambR (Hinterp τ (funOf envR t)) := by
  rw [Htyped, arrowR.app]
  simp only [comp.app]
  apply congrArg (funOf lambR)
  exact beta (Hinterp.isScottContinuous τ) (funOf envR t)

theorem typed (τ : LambTerm) :
    typed (Htyped τ) (arrowR envR lambR) :=
  typed.apply_retract
    (arrowR.isRetract envR.isRetract lambR.isRetract)

end Htyped

end DomainTheory.DataTypesAsLattices
