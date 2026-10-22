/-ai
Right uncurry, the inverse of right curry, sends a morphism from Y into the exponential of A and Z to a morphism from the tensor of A and Y to Z by transporting the product uncurry across the equality of product and tensor hom-types.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.exp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.prodHomToTensorHom
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryProduct
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
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

/-- Inverse of `curryRight`. -/
noncomputable def uncurryRight (A Y Z : InfoSysObj.{u}) (k : Y ⟶ InfoSysObj.exp A Z) :
    A ⊗ Y ⟶ Z :=
  prodHomToTensorHom A Y Z (uncurryProduct A Y Z k)

end InfoSys

end DomainTheory.InformationSystems
