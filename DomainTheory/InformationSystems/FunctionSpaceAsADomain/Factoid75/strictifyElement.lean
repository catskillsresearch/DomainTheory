/-ai
The strictification element of an element of the function space from A to B is the element of the strict function space obtained by strictifying the approximable map that corresponds to that element.
ai-/
module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictify
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict_strictify
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictFunctionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.approxMap_toStrictElement

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

/-- Scott’s retract map `|A → B| → |A →ₛ B|` induced by `strictify`. -/
def strictifyElement (x : (functionSystem A B).Element) :
    (strictFunctionSystem A B).Element :=
  approxMap_toStrictElement A B (strictify A B (element_toApproxMap A B x))
    (IsStrict_strictify A B _)

end InfoSys

end DomainTheory.InformationSystems
