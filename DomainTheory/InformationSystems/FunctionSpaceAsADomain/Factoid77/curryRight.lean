/-ai
The right curry of a morphism from the tensor product of A and Y into Z is a morphism from Y into the exponential of Z by A. It is the product curry of that morphism transported from a tensor hom to a map out of the product, which is Scott's curry after the swap.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.exp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorHomToProdHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj

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

attribute [instance] instCartesianMonoidalCategoryInfoSysObj

/-- `Hom(A ⊗ Y, Z) → Hom(Y, A → Z)` via Scott curry after swap. -/
noncomputable def curryRight (A Y Z : InfoSysObj.{u}) (h : A ⊗ Y ⟶ Z) :
    Y ⟶ InfoSysObj.exp A Z :=
  curryProduct A Y Z (tensorHomToProdHom A Y Z h)

end InfoSys

end DomainTheory.InformationSystems
