/-ai
The semantic factorization of the right-hand side identifies the elements of the sum of the lower-bound system with the product of the S-expression system with itself with the bottom-adjoined disjoint sum of the lower-bound domain and the product of the S-expression domain with itself. It composes the product isomorphism, lifted through a bottom-adjoined sum with the identity on the lower-bound domain, with the separated-sum isomorphism.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Hom.WithTopBot
import all Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.InformationSystems.Factoid24
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.PresentationDomains
public import DomainTheory.BridgeTheorems.InfoSysConstructions
public import DomainTheory.BridgeTheorems.ScottMapBridge
public import DomainTheory.BridgeTheorems.SexDomainEquation
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.lowerBoundSystem
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.SexSys
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.SexRhs

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open Order

/--
Semantic factor: `|A + (T × T)| ≃o WithBot (|A| ⊕ (|T| × |T|))` via the generic
product and separated-sum isos. Not the fixed-point equation itself.
-/
noncomputable def sexRhsSemanticIso :
    WithBot (lowerBoundSystem.Element ⊕ (SexSys.Element × SexSys.Element)) ≃o
      SexRhs.Element :=
  let ιProd := InfoSysConstructions.productDomainIso SexSys SexSys
  let ιSum := InfoSysConstructions.sumDomainIso lowerBoundSystem (productSystem SexSys SexSys)
  let mid :=
    (OrderIso.refl lowerBoundSystem.Element).sumCongr ιProd |>.withBotCongr
  mid.trans ιSum

end DomainTheory.BridgeTheorems
