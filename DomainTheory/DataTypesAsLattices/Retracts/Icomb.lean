module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Icomb : Pomega := graph (fun x => x)

namespace Icomb

theorem app (x : Pomega) : funOf Icomb x = x :=
  beta id_isScottContinuous x

theorem isGraph : Icomb = graph (fun x => funOf Icomb x) := by
  apply graph_ext
  intro x
  rw [Icomb.app]

theorem isRetract : Retract Icomb := by
  constructor
  change Icomb = graph (fun x => funOf Icomb (funOf Icomb x))
  have : (fun x => funOf Icomb (funOf Icomb x)) = fun x => x := by
    funext x
    simp [app]
  rw [this]
  rfl

end Icomb

end DomainTheory.DataTypesAsLattices
