/-ai
The cartesian monoidal category structure on information-system objects is the structure induced by the chosen terminal limit cone and the chosen binary-product limit cones.
ai-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.terminalLimitCone
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.productLimitCone

@[expose] public section

set_option linter.unusedSectionVars false

universe u

namespace DomainTheory.InformationSystems

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoSys

noncomputable abbrev instCartesianMonoidalCategoryInfoSysObj :
    CartesianMonoidalCategory.{u, u + 1} InfoSysObj.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalLimitCone productLimitCone

attribute [instance] instCartesianMonoidalCategoryInfoSysObj

end InfoSys

end DomainTheory.InformationSystems
