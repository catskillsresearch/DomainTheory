/-ai
The conditional of elements x and y evaluates to x at the Boolean element true and to y at the Boolean element false, and every strict approximable map from the Boolean system is the conditional of its values at true and false.

The three clauses are the two evaluation lemmas and the uniqueness lemma for strict Boolean maps.
ai-/
module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_toElement_boolTrue
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_toElement_boolFalse
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_unique

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)


























open ApproximableMap













/-- Domain isomorphism data: `A × A ≅ (BOOL →ₛ A)` via `cond`. -/
theorem conditional_iso (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x ∧
    (condMap A x y).toElement boolFalse = y ∧
    ∀ (f : ApproximableMap boolSystem A), IsStrict boolSystem A f →
      f = condMap A (f.toElement boolTrue) (f.toElement boolFalse) :=
  ⟨condMap_toElement_boolTrue A x y, condMap_toElement_boolFalse A x y,
    fun f hf => condMap_unique A f hf⟩

end InfoSys
end DomainTheory.InformationSystems
