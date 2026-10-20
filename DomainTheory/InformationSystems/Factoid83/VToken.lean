/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- Data objects of `V`: bottom `Δ`, top `∇`, and product left/right copies. -/
inductive VToken where
  | bot : VToken
  | top : VToken
  | pairL : VToken → VToken
  | pairR : VToken → VToken
  deriving DecidableEq

end InfoSys
end DomainTheory.InformationSystems
