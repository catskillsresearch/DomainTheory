module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.unit
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj

@[expose] public section

set_option linter.unusedSectionVars false

universe u

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace InfoSys

attribute [instance] InfoSysObj.decEq

open ApproximableMap

attribute [instance] instCategoryInfoSysObj

def terminalLimitCone : LimitCone (Functor.empty.{0} InfoSysObj.{u}) where
  cone := asEmptyCone InfoSysObj.unit
  isLimit := IsTerminal.ofUniqueHom
    (fun (X : InfoSysObj.{u}) => constMap (A := X.sys) unitSystem.botElement)
    fun (_X : InfoSysObj.{u}) m => approxMap_to_unit_eq_const m

end InfoSys

end DomainTheory.InformationSystems
