/-ai
The integer retract is a retract.

The retract equation says that the integer retract equals the graph of applying it twice. Rewrite by the graph equation and compare graphs. At each argument the two sides agree by the symmetric idempotence law.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.intR_idem
public import DomainTheory.DataTypesAsLattices.Retracts.intR_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem intR_isRetract : IsRetract intR := by
  change intR = graph (fun x => funOf intR (funOf intR x))
  refine intR_isGraph.trans ?_
  apply graph_ext
  intro x
  exact (intR_idem x).symm

end DomainTheory.DataTypesAsLattices
