/-ai
A lambda-definable map in one free variable is Scott continuous, so clause (iii) of Theorem 2.6 lands in the setting of clauses (i) and (ii). The one-variable interpretation of a term, with every other variable sent to bottom, is Scott continuous.

This is theorem_2_1 applied to the term, the constantly bottom environment, and the free index 0.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- LAMBDA-definable maps (in one free variable) are continuous, so
clause (iii) of Theorem 2.6 lands in the setting of (i)–(ii). -/
theorem theorem_2_6_lambda_continuous (t : Term) :
    IsScottContinuous (fun v => interp t (envSet (fun _ => botElem) 0 v)) :=
  theorem_2_1 t (fun _ => botElem) 0

end DomainTheory.DataTypesAsLattices
