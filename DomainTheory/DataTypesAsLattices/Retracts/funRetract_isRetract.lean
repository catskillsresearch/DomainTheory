/-ai
The function retract is a retract.

Two graph extensionalities and two applications of the function retract reduce the equation to the reverse of β-conversion for application of u.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.funRetract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem funRetract_isRetract : IsRetract funRetract := by
  apply graph_ext
  intro u
  rw [funRetract_app, funRetract_app]
  apply graph_ext
  intro x
  exact (beta (funOf_isScottContinuous u) x).symm

end DomainTheory.DataTypesAsLattices
