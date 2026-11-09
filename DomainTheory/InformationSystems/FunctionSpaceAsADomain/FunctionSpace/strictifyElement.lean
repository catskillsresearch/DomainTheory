module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.theorem_7_2
public import DomainTheory.InformationSystems.InformationSystems.a_second_example
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.strictify
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.IsStrict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.strictFunctionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.approxMap_toStrictElement

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

def strictifyElement (x : (functionSystem A B).Element) :
    (strictFunctionSystem A B).Element :=
  approxMap_toStrictElement A B (strictify A B (element_toApproxMap A B x))
    (IsStrict.strictify A B _)

end InfoSys

end DomainTheory.InformationSystems
