/-ai
The second projection of the swapped product, applied to the swap of a product element, equals the first projection of that element.

The elementwise composition law rewrites the left-hand side as the composite of the swap with the second projection, and that composite is the first projection.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_swap_snd

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace InfoSys

attribute [instance] InfoSysObj.decEq

namespace ApproximableMap

theorem swap_snd_toElement {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) (p : (productSystem A B).Element) :
    (sndMap B A).toElement ((swapMap A B).toElement p) = (fstMap A B).toElement p := by
  rw [← acomp_toElement, acomp_swap_snd]

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
