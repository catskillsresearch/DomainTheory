module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def funRetract : Pomega :=
  graph (fun u => graph (fun x => funOf u x))

namespace funRetract

theorem app (u : Pomega) :
    funOf funRetract u = graph (fun x => funOf u x) :=
  beta (graph_const_isScottContinuous (fun u x => funOf u x)
    (fun x => funOf.isScottContinuous_left x)) u

theorem isRetract : Retract funRetract := by
  constructor
  apply graph_ext
  intro u
  rw [funRetract.app, funRetract.app]
  apply graph_ext
  intro x
  exact (beta (funOf.isScottContinuous u) x).symm

end funRetract

end DomainTheory.DataTypesAsLattices
