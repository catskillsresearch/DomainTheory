/-ai
The abstraction clause is the right injection of the graph of those x for which the recursive call, on the first payload component, is taken in the environment updated by the value x at the zeroth payload component.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.inrightC
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload
public import DomainTheory.DataTypesAsLattices.Functionality.hApply
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def hLam (H e t : Pomega) : Pomega :=
  funOf inrightC
    (graph (fun x =>
      hApply H (funOf (expPayload e) (ofNat 1))
        (updateEnvUnion t x (funOf (expPayload e) (ofNat 0)))))

end DomainTheory.DataTypesAsLattices
