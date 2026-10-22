/-ai
The conditional element of a pair in the product of an information system with itself is the element of the strict function space from the Boolean system determined by the conditional map of the pair's first and second components.
ai-/
module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictFunctionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.approxMap_toStrictElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict_condMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

/-- `cond` as an element of `|BOOL →ₛ A|`. -/
def condElement (z : (productSystem A A).Element) :
    (strictFunctionSystem boolSystem A).Element :=
  approxMap_toStrictElement boolSystem A
    (condMap A ((fstMap A A).toElement z) ((sndMap A A).toElement z))
    (IsStrict_condMap A _ _)

end InfoSys

end DomainTheory.InformationSystems
