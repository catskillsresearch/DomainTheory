module

public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Kcomb_app_isGraph (x : Pomega) :
    funOf Kcomb x = graph (fun y => funOf (funOf Kcomb x) y) := by
  rw [Kcomb_app]
  apply graph_ext
  intro y
  exact (beta (const_isScottContinuous x) y).symm

end DomainTheory.DataTypesAsLattices
