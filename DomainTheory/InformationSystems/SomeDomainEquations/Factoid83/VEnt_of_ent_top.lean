/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- If `u ⊢ ∇`, then `u` entails every token (rogue top). -/
theorem VEnt_of_ent_top {u : Finset VToken} (h : VEnt u .top) (c : VToken) :
    VEnt u c := by
  match c with
  | .bot => exact VEnt.bot
  | .top => exact h
  | .pairL x =>
    cases h with
    | top_mem hm => exact VEnt.pairL_top hm
    | top_both hL _ => exact VEnt.pairL_proj (VEnt_of_ent_top hL x)
  | .pairR y =>
    cases h with
    | top_mem hm => exact VEnt.pairR_top hm
    | top_both _ hR => exact VEnt.pairR_proj (VEnt_of_ent_top hR y)

end InfoSys

end DomainTheory.InformationSystems
