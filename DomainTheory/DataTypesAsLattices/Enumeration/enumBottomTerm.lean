module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_14
public import DomainTheory.DataTypesAsLattices.Graph.funOf

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def enumBottomTerm : Term :=
  .app (.lam 9 (.app (.var 9) (.var 9)))
    (.lam 9 (.app (.var 9) (.var 9)))

namespace enumBottomTerm

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem avoids (i : ℕ) : enumBottomTerm.Avoids i := by
  unfold enumBottomTerm
  constructor <;>
    (by_cases h : 9 = i
     · exact Or.inl h
     · exact Or.inr ⟨h, h⟩)

theorem interp (ρ : ℕ → Pomega) :
    _root_.DomainTheory.DataTypesAsLattices.interp enumBottomTerm ρ = botElem := by
  simp only [enumBottomTerm, _root_.DomainTheory.DataTypesAsLattices.interp, envSet,
    Function.update]
  exact _root_.DomainTheory.DataTypesAsLattices.eq_2_14

end enumBottomTerm

end DomainTheory.DataTypesAsLattices
