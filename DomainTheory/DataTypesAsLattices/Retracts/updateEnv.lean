/-ai
The environment update of Scott 1976, (4.41), sends an element t, an element x, and a natural number n to the graph of the function that returns x at the code of n and returns the m-th section of t at every other natural number m.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.41).** Environment update `t[x/n]`. -/
def updateEnv (t x : Pomega) (n : ℕ) : Pomega :=
  graph (fun m => if m = ofNat n then x else funOf t m)

end DomainTheory.DataTypesAsLattices
