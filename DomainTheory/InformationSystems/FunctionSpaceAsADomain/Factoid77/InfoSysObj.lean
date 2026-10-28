module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

universe u

namespace DomainTheory.InformationSystems
namespace InfoSys

open DomainTheory.InformationSystems.Constructive
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

structure InfoSysObj : Type (u + 1) where
  Token : Type u
  [decEq : DecidableEq Token]
  sys : InfoSys Token

end InfoSys
end DomainTheory.InformationSystems
