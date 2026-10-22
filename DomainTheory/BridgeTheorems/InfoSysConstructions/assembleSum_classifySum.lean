/-ai
Assembling the classification of a sum-domain element recovers that element.

The classification is a chosen separated-sum code that assembles to the element, and the chosen witness is exactly this equality.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.exists_assembleSum_eq
public import DomainTheory.BridgeTheorems.InfoSysConstructions.classifySum

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem assembleSum_classifySum (z : (sumSystem A B).Element) :
    assembleSum A B (classifySum A B z) = z :=
  Classical.choose_spec (exists_assembleSum_eq A B z)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
