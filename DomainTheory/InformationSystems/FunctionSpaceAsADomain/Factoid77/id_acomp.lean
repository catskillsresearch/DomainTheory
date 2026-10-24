module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoSys

attribute [instance] InfoSysObj.decEq

namespace ApproximableMap

theorem id_acomp {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : InfoSys α} {B : InfoSys β} (f : ApproximableMap A B) :
    acomp (idMap A) f = f :=
  (ext_iff_toElement _ _).2 fun x => by rw [acomp.toElement, idMap.toElement]

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
