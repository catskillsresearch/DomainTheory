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

namespace ApproximableMap

theorem curry_uncurry {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)
    (k : ApproximableMap A (functionSystem B C)) :
    curryMap A B C (uncurryMap A B C k) = k :=
  Eq.symm (curryMap_unique A B C (uncurryMap A B C k) k rfl)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
