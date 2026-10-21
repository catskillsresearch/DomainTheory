/-ai
Classification sends an element of the separated-sum system to a bottom-adjoined disjoint-sum code by choosing, classically, a code that assembles to it.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.exists_assembleSum_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

/-- Classify a sum-domain element as `WithBot (|A| ⊕ |B|)`. Classical. -/
noncomputable def classifySum (z : (sumSystem A B).Element) :
    WithBot (A.Element ⊕ B.Element) :=
  Classical.choose (exists_assembleSum_eq A B z)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
