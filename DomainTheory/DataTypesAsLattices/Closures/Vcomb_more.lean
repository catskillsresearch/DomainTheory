module

public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_19
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace Vcomb

theorem isRetract : Retract Vcomb := by
  constructor
  change Vcomb = graph (fun a => funOf Vcomb (funOf Vcomb a))
  apply graph_ext
  intro a
  exact (Vcomb.app a).symm.trans
    (_root_.DomainTheory.DataTypesAsLattices.eq_5_19 a).symm

end Vcomb

end DomainTheory.DataTypesAsLattices
