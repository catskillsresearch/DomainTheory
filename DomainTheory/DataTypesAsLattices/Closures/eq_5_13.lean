module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Closures.boxShift
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_5_13 (a b : Pomega) :
    boxPlus a b = graph (fun u =>
      dcondSet (condSet (squareFst u) (ofNat 0) (ofNat 0) ∪
          condSet (squareSnd u) (ofNat 1) (ofNat 1))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u)))) :=
  rfl

end DomainTheory.DataTypesAsLattices
