module

public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_mid_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Scomb_app_isGraph (f : Pomega) :
    funOf Scomb f = graph (fun g => funOf (funOf Scomb f) g) := by
  rw [Scomb_app]
  apply graph_ext
  intro g
  exact (beta (Scomb_mid_isScottContinuous f) g).symm

end DomainTheory.DataTypesAsLattices
