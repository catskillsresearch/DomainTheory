/-ai
The limit cone of the empty diagram in the category of information-system objects is the cone on the unit object. The morphism from an object X is the constant approximable map onto the bottom element of the unit system, and every morphism into the unit equals that constant map.
ai-/

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
