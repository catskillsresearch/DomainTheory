module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.a_second_example
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictFunctionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.approxMap_toStrictElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

def condElement (z : (productSystem A A).Element) :
    (strictFunctionSystem boolSystem A).Element :=
  approxMap_toStrictElement boolSystem A
    (condMap A ((productSystem.fstMap A A).toElement z) ((productSystem.sndMap A A).toElement z))
    (IsStrict.condMap A _ _)

end InfoSys

end DomainTheory.InformationSystems
