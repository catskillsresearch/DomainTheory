module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj

@[expose] public section


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





attribute [instance] instCartesianMonoidalCategoryInfoSysObj

theorem tensorObj_eq_prod (A Y : InfoSysObj.{u}) : A ⊗ Y = InfoSysObj.prod A Y := rfl

end InfoSys
end DomainTheory.InformationSystems
