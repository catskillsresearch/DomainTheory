/-ai
An information-system object consists of a token type, a decidable equality on that type, and an information system with those tokens.
ai-/
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

/-- Bundled information system (object of the Scott category). -/
structure InfoSysObj : Type (u + 1) where
  Token : Type u
  [decEq : DecidableEq Token]
  sys : InfoSys Token

end InfoSys
end DomainTheory.InformationSystems
