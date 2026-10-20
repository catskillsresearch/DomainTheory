/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Factoid83.VToken
public import DomainTheory.InformationSystems.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.Factoid83.vPairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- Entailment on `V` (Scott (3)–(6)). -/
inductive VEnt : Finset VToken → VToken → Prop where
  | bot {u : Finset VToken} : VEnt u .bot
  | top_mem {u : Finset VToken} (h : .top ∈ u) : VEnt u .top
  | top_both {u : Finset VToken}
      (hL : VEnt (vPairLFinset u) .top) (hR : VEnt (vPairRFinset u) .top) :
      VEnt u .top
  | pairL_top {u : Finset VToken} {x : VToken} (h : .top ∈ u) : VEnt u (.pairL x)
  | pairL_proj {u : Finset VToken} {x : VToken}
      (h : VEnt (vPairLFinset u) x) : VEnt u (.pairL x)
  | pairR_top {u : Finset VToken} {y : VToken} (h : .top ∈ u) : VEnt u (.pairR y)
  | pairR_proj {u : Finset VToken} {y : VToken}
      (h : VEnt (vPairRFinset u) y) : VEnt u (.pairR y)

end InfoSys
end DomainTheory.InformationSystems
