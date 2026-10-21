/-ai
The hom-set equivalence is natural in the middle variable: the image of left tensoring by A applied to f, followed by g, equals f followed by the image of g.

Injectivity of the inverse equivalence reduces the claim to an equality of uncurried maps. Unfolding the equivalence, the composition law for right uncurry applied to the curry of g, and the round trip from curry back through uncurry, identify the two sides.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.curryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight_curryRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.tensorExpEquiv
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.uncurryRight_comp_left
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

theorem tensorExpEquiv_natural (A : InfoSysObj.{u}) {Y' Y Z : InfoSysObj.{u}}
    (f : Y' ⟶ Y) (g : A ⊗ Y ⟶ Z) :
    tensorExpEquiv A Y' Z ((tensorLeft A).map f ≫ g) =
      f ≫ tensorExpEquiv A Y Z g := by
  apply (tensorExpEquiv A Y' Z).symm.injective
  change uncurryRight A Y' Z
      (tensorExpEquiv A Y' Z ((tensorLeft A).map f ≫ g)) =
    uncurryRight A Y' Z (f ≫ tensorExpEquiv A Y Z g)
  simp only [tensorExpEquiv, Equiv.coe_fn_mk]
  have h := uncurryRight_comp_left A f (curryRight A Y Z g)
  rw [uncurryRight_curryRight] at h
  rw [uncurryRight_curryRight, h]

end InfoSys

end DomainTheory.InformationSystems
