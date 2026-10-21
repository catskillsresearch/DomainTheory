/-ai
The integer retract equals the graph of its own application.

Rewrite by the symmetric form of the equation identifying the integer retract with the integer functional applied to it, then compare graphs. At each argument the two sides agree by the symmetric application law.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.intR_eq_intF
public import DomainTheory.DataTypesAsLattices.Retracts.intR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































theorem intR_isGraph : intR = graph (funOf intR) := by
  refine intR_eq_intF.symm.trans ?_
  apply graph_ext
  intro u
  exact (intR_app u).symm

end DomainTheory.DataTypesAsLattices
