module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_14
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.graph

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- A closed divergent term denoting bottom. -/
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
