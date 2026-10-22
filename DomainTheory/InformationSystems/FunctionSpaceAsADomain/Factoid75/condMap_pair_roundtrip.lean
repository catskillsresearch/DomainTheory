/-ai
The conditional map of elements x and y evaluates to x at the Boolean element true and to y at the Boolean element false.

The two equalities are the corresponding evaluation lemmas.
ai-/
module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_toElement_boolTrue
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_toElement_boolFalse

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


/-- One direction of the conditional isomorphism on pairs. -/
theorem condMap_pair_roundtrip (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x ∧
    (condMap A x y).toElement boolFalse = y :=
  ⟨condMap_toElement_boolTrue A x y, condMap_toElement_boolFalse A x y⟩

end InfoSys
end DomainTheory.InformationSystems
