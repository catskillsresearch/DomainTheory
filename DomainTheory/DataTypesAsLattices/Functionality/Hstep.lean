/-ai
One continuous step of (4.43), dispatched on the tags of (4.44). The step at an interpreter, an expression, and an environment is the nested definite conditional on the expression tag and its successive predecessors, selecting the variable, zero, successor, predecessor, conditional, application, or abstraction clause, and returning the top element when none of those tests succeed.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.expTag
public import DomainTheory.DataTypesAsLattices.Functionality.hVar
public import DomainTheory.DataTypesAsLattices.Functionality.hZero
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc
public import DomainTheory.DataTypesAsLattices.Functionality.hPred
public import DomainTheory.DataTypesAsLattices.Functionality.hCond
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Functionality.hLam

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- One continuous step of (4.43), dispatched on the (4.44) tags. -/
def Hstep (H e t : Pomega) : Pomega :=
  dcondSet (expTag e) (hVar e t)
    (dcondSet (predSet (expTag e)) hZero
      (dcondSet (predSet (predSet (expTag e))) (hSucc H e t)
        (dcondSet (predSet^[3] (expTag e)) (hPred H e t)
          (dcondSet (predSet^[4] (expTag e)) (hCond H e t)
            (dcondSet (predSet^[5] (expTag e)) (hApp H e t)
              (dcondSet (predSet^[6] (expTag e)) (hLam H e t)
                topElem))))))

end DomainTheory.DataTypesAsLattices
