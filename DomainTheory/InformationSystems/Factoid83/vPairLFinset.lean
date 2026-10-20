/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Factoid83.VToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

private def pairLInsert : VToken → Finset VToken → Finset VToken
  | .pairL t => insert t
  | .bot | .top | .pairR _ => id

private instance :
    LeftCommutative (pairLInsert : VToken → Finset VToken → Finset VToken) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

/-- Left projection: `{X | (X, Δ) ∈ u}`. -/
def vPairLFinset (u : Finset VToken) : Finset VToken :=
  Multiset.foldr pairLInsert (∅ : Finset VToken) u.1

end InfoSys
end DomainTheory.InformationSystems
