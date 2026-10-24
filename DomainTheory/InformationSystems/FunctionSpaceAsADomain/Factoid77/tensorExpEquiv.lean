module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.exp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryRight_uncurryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoSys

open ApproximableMap
attribute [instance] InfoSysObj.decEq
attribute [instance] instCategoryInfoSysObj
attribute [instance] instCartesianMonoidalCategoryInfoSysObj

/-- Hom-set equivalence for the exponential (Scott curry after braiding). -/
noncomputable def tensorExpEquiv (A : InfoSysObj.{u}) (Y Z : InfoSysObj.{u}) :
    (A ⊗ Y ⟶ Z) ≃ (Y ⟶ InfoSysObj.exp A Z) where
  toFun := curryRight A Y Z
  invFun := uncurryRight A Y Z
  left_inv := uncurryRight.curryRight A Y Z
  right_inv := curryRight_uncurryRight A Y Z

theorem tensorExpEquiv.natural (A : InfoSysObj.{u}) {Y' Y Z : InfoSysObj.{u}}
    (f : Y' ⟶ Y) (g : A ⊗ Y ⟶ Z) :
    tensorExpEquiv A Y' Z ((tensorLeft A).map f ≫ g) =
      f ≫ tensorExpEquiv A Y Z g := by
  apply (tensorExpEquiv A Y' Z).symm.injective
  change uncurryRight A Y' Z
      (tensorExpEquiv A Y' Z ((tensorLeft A).map f ≫ g)) =
    uncurryRight A Y' Z (f ≫ tensorExpEquiv A Y Z g)
  simp only [tensorExpEquiv, Equiv.coe_fn_mk]
  have h := uncurryRight.comp_left A f (curryRight A Y Z g)
  rw [uncurryRight.curryRight] at h
  rw [uncurryRight.curryRight, h]

end InfoSys


end DomainTheory.InformationSystems
