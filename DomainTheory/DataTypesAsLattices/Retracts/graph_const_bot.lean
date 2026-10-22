module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem graph_const_bot : graph (fun _ => botElem) = botElem := by
  ext p
  simp [graph, botElem]

end DomainTheory.DataTypesAsLattices
