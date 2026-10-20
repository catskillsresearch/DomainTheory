/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid26

/-- Tokens: `bot` ≃ `Δ`, or a graph atom `pair a b`. -/
inductive Token (A B : Type*) where
  | bot
  | pair (a : A) (b : B)
  deriving DecidableEq

end Factoid26
end DomainTheory.InformationSystems
