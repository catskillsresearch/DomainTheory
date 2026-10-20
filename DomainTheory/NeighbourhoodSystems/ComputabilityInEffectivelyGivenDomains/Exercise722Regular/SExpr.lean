/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- **The syntax of `S`-terms** (Scott's four generators): `Σ`, a singleton `{σ}`, concatenation
`X·Y`, and intersection `X ∩ Y`. A fragment of regular expressions with `·` and `∩` and the
universal language `Σ`, but no union / complement / star. -/
inductive SExpr : Type
  | sigma : SExpr
  | single : List Bool → SExpr
  | cat : SExpr → SExpr → SExpr
  | cap : SExpr → SExpr → SExpr
  deriving DecidableEq

end Exercise722
end DomainTheory.NeighbourhoodSystems
