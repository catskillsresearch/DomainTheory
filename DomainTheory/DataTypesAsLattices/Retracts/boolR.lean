module

public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.dcondSet_bool_idem
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def boolR : Pomega :=
  graph (fun u => dcondSet u (ofNat 0) (ofNat 1))

namespace boolR

theorem app (u : Pomega) :
    funOf boolR u = dcondSet u (ofNat 0) (ofNat 1) :=
  beta (dcondSet.isScottContinuous_left (ofNat 0) (ofNat 1)) u

theorem isRetract : Retract boolR := by
  constructor
  apply graph_ext
  intro u
  rw [app, app, dcondSet_bool_idem]

end boolR

end DomainTheory.DataTypesAsLattices
