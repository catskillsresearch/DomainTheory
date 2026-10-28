
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoSys

attribute [instance] InfoSysObj.decEq

namespace ApproximableMap

theorem swap_fst_toElement {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) (p : (productSystem A B).Element) :
    (fstMap B A).toElement ((swapMap A B).toElement p) = (sndMap A B).toElement p := by
  rw [← acomp.toElement, acomp.swap_fst]

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
