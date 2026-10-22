/-ai
The exponential functor at an object A sends an object Z to the exponential of Z by A.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj

@[expose] public section


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


theorem expFunctor_obj (A Z : InfoSysObj.{u}) :
    (expFunctor A).obj Z = InfoSysObj.exp A Z :=
  rfl

end InfoSys
end DomainTheory.InformationSystems
