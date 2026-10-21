/-ai
The second projection, after the pairing of the first projection with the composite of the second projection and a map f, equals f evaluated at the second projection of the input element.

That pairing composed diagrammatically with the second projection equals the second projection composed with f. The value of the first composite is the value of the second, and diagrammatic composition then evaluates as f at the second projection.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_toElement
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

theorem lift_snd_toElement (A : InfoSysObj.{u}) {Y Y' : InfoSysObj.{u}}
    (f : Y' ⟶ Y) (p : (productSystem A.sys Y'.sys).Element) :
    (sndMap A.sys Y.sys).toElement
        ((pairMap A.sys Y.sys (fstMap A.sys Y'.sys)
            (acomp (sndMap A.sys Y'.sys) f)).toElement p) =
      f.toElement ((sndMap A.sys Y'.sys).toElement p) := by
  have e :
      acomp (pairMap A.sys Y.sys (fstMap A.sys Y'.sys) (acomp (sndMap A.sys Y'.sys) f))
        (sndMap A.sys Y.sys) =
      acomp (sndMap A.sys Y'.sys) f := by
    simp only [acomp, comp_sndMap_pairMap]
  calc
    (sndMap A.sys Y.sys).toElement
        ((pairMap A.sys Y.sys (fstMap A.sys Y'.sys)
          (acomp (sndMap A.sys Y'.sys) f)).toElement p) =
      (acomp (pairMap A.sys Y.sys (fstMap A.sys Y'.sys)
        (acomp (sndMap A.sys Y'.sys) f)) (sndMap A.sys Y.sys)).toElement p :=
      (acomp_toElement _ _ _).symm
    _ = (acomp (sndMap A.sys Y'.sys) f).toElement p := congrArg (fun φ => φ.toElement p) e
    _ = f.toElement ((sndMap A.sys Y'.sys).toElement p) := acomp_toElement _ _ _

end InfoSys

end DomainTheory.InformationSystems
