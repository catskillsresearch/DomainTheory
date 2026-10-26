module

public import DomainTheory.DataTypesAsLattices.Retracts.boolR
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.dcondSet_bool_idem

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace boolR

theorem isRetract : Retract boolR := by
  constructor
  apply graph_ext
  intro u
  rw [app, app, dcondSet_bool_idem]

end boolR

end DomainTheory.DataTypesAsLattices
