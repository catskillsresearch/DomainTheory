module

public import DomainTheory.DataTypesAsLattices.Functionality.Z
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Graph.funOf_isScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Z.isScottContinuous_left (n : ℕ) (x : Pomega) :
    IsScottContinuous (fun f => Z n f x) := by
  induction n with
  | zero => simpa [Z] using const_isScottContinuous x
  | succ n ih =>
    simpa [Z] using
      continuous_tuple
        (fun y => funOf.isScottContinuous_left y)
        (fun u => funOf_isScottContinuous u)
        id_isScottContinuous ih

end DomainTheory.DataTypesAsLattices
