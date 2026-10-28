module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
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
def acomp {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}
    (f : ApproximableMap A B) (g : ApproximableMap B C) : ApproximableMap A C :=
  ApproximableMap.comp g f

theorem acomp.swap_fst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    acomp (swapMap A B) (fstMap B A) = sndMap A B := by
  simp only [acomp, swapMap, comp_fstMap_pairMap]

theorem acomp.swap_snd {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    acomp (swapMap A B) (sndMap B A) = fstMap A B := by
  simp only [acomp, swapMap, comp_sndMap_pairMap]

theorem acomp.toElement {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}
    (f : ApproximableMap A B) (g : ApproximableMap B C) (x : A.Element) :
    (acomp f g).toElement x = g.toElement (f.toElement x) :=
  comp.toElement g f x

theorem acomp.assoc {α β γ δ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ} {D : InfoSys δ}
    (f : ApproximableMap A B) (g : ApproximableMap B C) (h : ApproximableMap C D) :
    acomp (acomp f g) h = acomp f (acomp g h) :=
  (ext_iff_toElement _ _).2 fun x => by simp only [acomp.toElement]

theorem acomp.id {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : InfoSys α} {B : InfoSys β} (f : ApproximableMap A B) :
    acomp f (idMap B) = f :=
  (ext_iff_toElement _ _).2 fun x => by rw [acomp.toElement, idMap.toElement]

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
