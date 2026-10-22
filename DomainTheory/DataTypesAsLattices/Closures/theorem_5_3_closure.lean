module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_3
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_arrowR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem theorem_5_3_closure {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (arrowR a b) :=
  ⟨⟨Icomb_subset_arrowR ha hb, theorem_5_3 ha hb⟩⟩

end DomainTheory.DataTypesAsLattices
