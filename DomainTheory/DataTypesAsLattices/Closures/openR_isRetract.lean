module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.openR
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
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
