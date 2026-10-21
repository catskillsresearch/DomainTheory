/-ai
Left tensoring by A sends a morphism f to the pairing of the first projection with the second projection composed with f, transported from product maps to tensor maps.

By uniqueness of pairing it is enough that the tensor image composed with the first projection of the target is the first projection of the source, and that it composed with the second projection is the second projection composed with f. Those are the whiskering identities for the two projections in a cartesian monoidal category.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.productMapToTensorMap
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

/-- `A ◁ f` is the pairing `⟨fst, snd ≫ f⟩`. -/
theorem tensorLeft_map_eq (A : InfoSysObj.{u}) {Y Y' : InfoSysObj.{u}} (f : Y ⟶ Y') :
    (tensorLeft A).map f =
      productMapToTensorMap A Y Y'
        (pairMap A.sys Y'.sys (fstMap A.sys Y.sys)
          (acomp (sndMap A.sys Y.sys) f)) := by
  refine pairMap_unique A.sys Y'.sys
      (fstMap A.sys Y.sys) (acomp (sndMap A.sys Y.sys) f)
      ((tensorLeft A).map f) ?_ ?_
  · change ((tensorLeft A).map f) ≫ fstMap A.sys Y'.sys = fstMap A.sys Y.sys
    exact CartesianMonoidalCategory.whiskerLeft_fst (X := A) (Y := Y) (Z := Y') f
  · change ((tensorLeft A).map f) ≫ sndMap A.sys Y'.sys = sndMap A.sys Y.sys ≫ f
    exact CartesianMonoidalCategory.whiskerLeft_snd (X := A) (Y := Y) (Z := Y') f

end InfoSys

end DomainTheory.InformationSystems
