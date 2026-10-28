module

public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_inner_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app2

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Scomb_app2_isGraph (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf (funOf Scomb f) g) x) := by
  rw [Scomb_app2]
  apply graph_ext
  intro x
  exact (beta (Scomb_inner_isScottContinuous f g) x).symm

end DomainTheory.DataTypesAsLattices
