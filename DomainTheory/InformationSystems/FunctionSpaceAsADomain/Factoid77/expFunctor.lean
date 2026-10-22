/-ai
The exponential functor at an information-system object A is the right adjoint of left tensoring with A induced by the tensor-exponential equivalence. The naturality required by that construction is the naturality of the equivalence.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorExpEquiv
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorExpEquiv_natural
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

/-- Right adjoint to `tensorLeft A` from the curry equivalence. -/
noncomputable def expFunctor (A : InfoSysObj.{u}) : InfoSysObj.{u} ⥤ InfoSysObj.{u} :=
  Adjunction.rightAdjointOfEquiv (F := tensorLeft A) (tensorExpEquiv A)
    fun _Y' _Y _Z f g => by
      simpa using tensorExpEquiv_natural A f g

end InfoSys

end DomainTheory.InformationSystems
