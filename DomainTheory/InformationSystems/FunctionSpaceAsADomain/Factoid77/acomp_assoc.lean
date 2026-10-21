/-ai
Diagrammatic composition of approximable maps is associative.

The two associations agree on every element, because the elementwise evaluation of diagrammatic composition simplifies to the same nested application.
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

theorem acomp_assoc {α β γ δ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ} {D : InfoSys δ}
    (f : ApproximableMap A B) (g : ApproximableMap B C) (h : ApproximableMap C D) :
    acomp (acomp f g) h = acomp f (acomp g h) :=
  (ext_iff_toElement _ _).2 fun x => by simp only [acomp_toElement]

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
