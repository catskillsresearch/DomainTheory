module

public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb
public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Enumeration.Lterm
public import DomainTheory.DataTypesAsLattices.Enumeration.Lterm_more
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.FUN
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
public import DomainTheory.DataTypesAsLattices.Enumeration.graph_mem_FUN

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace Lcomb

theorem app (x : Pomega) :
    funOf Lcomb x = funOf (funOf x (ofNat 1)) (funOf x (ofNat 2)) :=
  beta (theorem_1_3.tuple
    (fun y => funOf.isScottContinuous_left y)
    (fun t => funOf.isScottContinuous t)
    (funOf.isScottContinuous_left (ofNat 1))
    (funOf.isScottContinuous_left (ofNat 2))) x

theorem combinatory : IsCombinatory Lcomb := by
  rw [← Lterm.interp]
  exact theorem_2_4.closed Lterm

theorem mem_FUN : Lcomb ∈ FUN :=
  graph_mem_FUN (theorem_1_3.tuple
    (fun y => funOf.isScottContinuous_left y)
    (fun t => funOf.isScottContinuous t)
    (funOf.isScottContinuous_left (ofNat 1))
    (funOf.isScottContinuous_left (ofNat 2)))

end Lcomb

end DomainTheory.DataTypesAsLattices
