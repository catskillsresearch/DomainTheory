module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

























theorem Z_graph_funOf (n : ℕ) (f x : Pomega) :
    Z n (graph (fun y => funOf f y)) x = Z n f x := by
  induction n with
  | zero => simp [Z]
  | succ n ih =>
    simp [Z, ih]
    have : funOf (graph (fun y => funOf f y)) (Z n f x) = funOf f (Z n f x) :=
      beta (funOf_isScottContinuous f) (Z n f x)
    exact this

end DomainTheory.DataTypesAsLattices
