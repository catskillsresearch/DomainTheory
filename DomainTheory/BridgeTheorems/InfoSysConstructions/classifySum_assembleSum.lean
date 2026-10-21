/-ai
Classifying the assembly of a separated-sum code recovers that code.

Assembly is injective, and assembling the classification of an assembly returns that assembly.
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
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.classifySum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum_classifySum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum_injective

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem classifySum_assembleSum (w : WithBot (A.Element ⊕ B.Element)) :
    classifySum A B (assembleSum A B w) = w := by
  apply assembleSum_injective A B
  exact assembleSum_classifySum A B (assembleSum A B w)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
