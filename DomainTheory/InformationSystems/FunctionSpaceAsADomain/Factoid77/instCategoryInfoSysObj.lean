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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.id_acomp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_id
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.acomp_assoc

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

open ApproximableMap

abbrev instCategoryInfoSysObj : Category.{u, u + 1} InfoSysObj.{u} where
  Hom A B := ApproximableMap A.sys B.sys
  id A := idMap A.sys
  comp f g := acomp f g
  id_comp := id_acomp
  comp_id := acomp_id
  assoc := acomp_assoc

end InfoSys

end DomainTheory.InformationSystems
