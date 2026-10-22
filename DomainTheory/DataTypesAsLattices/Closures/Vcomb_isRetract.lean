
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_19

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Vcomb_isRetract : Retract Vcomb := by
  constructor
  change Vcomb = graph (fun a => funOf Vcomb (funOf Vcomb a))
  apply graph_ext
  intro a
  exact (Vcomb_app a).symm.trans (eq_5_19 a).symm

end DomainTheory.DataTypesAsLattices
