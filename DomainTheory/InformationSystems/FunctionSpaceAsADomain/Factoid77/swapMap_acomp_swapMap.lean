
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.theorem_7_2
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.id_acomp
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

theorem swapMap_acomp_swapMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    acomp (swapMap A B) (swapMap B A) = idMap (productSystem A B) := by
  have hfst : acomp (acomp (swapMap A B) (swapMap B A)) (productSystem.fstMap A B) = productSystem.fstMap A B := by
    calc
      acomp (acomp (swapMap A B) (swapMap B A)) (productSystem.fstMap A B)
          = acomp (swapMap A B) (acomp (swapMap B A) (productSystem.fstMap A B)) := acomp.assoc _ _ _
      _ = acomp (swapMap A B) (productSystem.sndMap B A) := by rw [acomp.swap_fst]
      _ = productSystem.fstMap A B := acomp.swap_snd A B
  have hsnd : acomp (acomp (swapMap A B) (swapMap B A)) (productSystem.sndMap A B) = productSystem.sndMap A B := by
    calc
      acomp (acomp (swapMap A B) (swapMap B A)) (productSystem.sndMap A B)
          = acomp (swapMap A B) (acomp (swapMap B A) (productSystem.sndMap A B)) := acomp.assoc _ _ _
      _ = acomp (swapMap A B) (productSystem.fstMap B A) := by rw [acomp.swap_snd]
      _ = productSystem.sndMap A B := acomp.swap_fst A B
  exact (pairMap.unique A B (productSystem.fstMap A B) (productSystem.sndMap A B) _ hfst hsnd).trans
    (pairMap.unique A B (productSystem.fstMap A B) (productSystem.sndMap A B) (idMap _)
      (id_acomp _) (id_acomp _)).symm

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
