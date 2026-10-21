/-ai
Evaluating, at the swap of a product element, the pairing of a map composed with the first projection and the second projection yields the pair whose components are that map at the swapped first projection and the swapped second projection.

The two sides have the same first projection and the same second projection, by the projection laws for a pairing and for a paired element.
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.exp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.swapMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCategoryInfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.instCartesianMonoidalCategoryInfoSysObj

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.fstMap_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.sndMap_pairElements
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

theorem pair_after_swap_toElement (A Y Z : InfoSysObj.{u})
    (φ : Y ⟶ InfoSysObj.exp A Z) (p : (productSystem A.sys Y.sys).Element) :
    (pairMap (functionSystem A.sys Z.sys) A.sys
        (ApproximableMap.comp φ (fstMap Y.sys A.sys))
        (sndMap Y.sys A.sys)).toElement ((swapMap A.sys Y.sys).toElement p) =
      pairElements (functionSystem A.sys Z.sys) A.sys
        (φ.toElement ((fstMap Y.sys A.sys).toElement ((swapMap A.sys Y.sys).toElement p)))
        ((sndMap Y.sys A.sys).toElement ((swapMap A.sys Y.sys).toElement p)) := by
  refine element_eq_of_fst_snd _ _ _ _ ?_ ?_
  · rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement]
    exact (fstMap_pairElements _ _ _ _).symm
  · rw [← comp_toElement, comp_sndMap_pairMap]
    exact (sndMap_pairElements _ _ _ _).symm

end InfoSys

end DomainTheory.InformationSystems
