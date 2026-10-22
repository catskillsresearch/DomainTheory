module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.openR_app
public import DomainTheory.DataTypesAsLattices.Closures.openR_idem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem openR_isRetract : Retract openR := by
  constructor
  change openR = graph (fun x => funOf openR (funOf openR x))
  apply graph_ext
  intro u
  rw [← openR_app]
  exact (openR_idem u).symm

end DomainTheory.DataTypesAsLattices
