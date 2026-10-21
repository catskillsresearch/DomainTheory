/-ai
The S-expression fixed-point isomorphism identifies the elements of the S-expression system with the elements of the right-hand side, the sum of the lower-bound system with the product of the S-expression system with itself. It is the tree domain isomorphism of the lower-bound system, induced by unfolding and folding tokens.
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

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open Order

/--
**S-expression fixed-point equation.** `|T| ≃o |A + (T × T)|`, the order
isomorphism of `SexSys.Element` with `SexRhs.Element` induced by
`treeUnfold` / `treeFold` (`treeDomainIso`).
-/
noncomputable def sexDomainEquationIso :
    SexSys.Element ≃o SexRhs.Element :=
  treeDomainIso lowerBoundSystem

end DomainTheory.BridgeTheorems
