/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- The standard truth-valuation semantics: `v : ℕ → Bool` assigns each variable a truth value. -/
def evalV (v : ℕ → Bool) : Formula → Bool
  | .var i => v i
  | .bot => false
  | .top => true
  | .neg φ => !(evalV v φ)
  | .and φ ψ => evalV v φ && evalV v ψ
  | .or φ ψ => evalV v φ || evalV v ψ

end DomainTheory.NeighbourhoodSystems
