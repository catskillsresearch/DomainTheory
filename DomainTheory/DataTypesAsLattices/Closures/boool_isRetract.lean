/-ai
The boolean map boool is a retract.

Extensionality of graphs reduces the retract equation to an equality of values. Two applications of the boolean action, followed by the idempotence of that conditional set, give the equality.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boool_app
public import DomainTheory.DataTypesAsLattices.Closures.boool_idem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boool_isRetract : IsRetract boool := by
  apply graph_ext
  intro u
  rw [boool_app, boool_app, boool_idem]

end DomainTheory.DataTypesAsLattices
