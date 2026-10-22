/-ai
Currying the uncurrying of a map into a function space recovers the map.

This is the symmetric form of the uniqueness lemma for currying, applied to that uncurrying and to the map, with a definitional equality.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.curryMap_unique
@[expose] public section


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
