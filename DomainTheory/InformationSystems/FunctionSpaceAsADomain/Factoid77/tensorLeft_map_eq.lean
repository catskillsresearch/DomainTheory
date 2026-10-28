
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
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
