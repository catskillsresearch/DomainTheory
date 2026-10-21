/-ai
Diagrammatic composition of approximable maps is ordinary composition with the two maps in the opposite order, so that the first map is applied and then the second.
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

def acomp {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}
    (f : ApproximableMap A B) (g : ApproximableMap B C) : ApproximableMap A C :=
  ApproximableMap.comp g f

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
