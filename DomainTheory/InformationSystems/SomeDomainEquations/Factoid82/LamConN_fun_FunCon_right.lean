/-ai
An explicit right-hand witness at stage n+1 gives the function clause at stage n: stage-n consistency of the input union of a subcollection of function tokens yields stage-n consistency of the output union.

The witness is applied to that subcollection and its input hypothesis.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)





















/-- FunCon from an explicit right-branch witness at stage `n+1`. -/
theorem LamConN_fun_FunCon_right {n : ℕ} {u : Finset (RawLamToken α)}
    (_hA : lamAtomFinset u = ∅)
    (_hWF : ∀ p ∈ lamFunFinset u,
      LamConN A n (listToFinset p.1) ∧ LamConN A n (listToFinset p.2))
    (hFun : ∀ s ⊆ lamFunFinset u,
      LamConN A n (lamInputUnion s) → LamConN A n (lamOutputUnion s))
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hIn : LamConN A n (lamInputUnion s)) :
    LamConN A n (lamOutputUnion s) :=
  hFun s hs hIn

end InfoSys
end DomainTheory.InformationSystems
