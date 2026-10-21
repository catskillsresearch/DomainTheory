/-ai
If a finite set of V-tokens entails top, then it entails every token. This is the rogue-top property.

Match on the conclusion. Bottom is entailed outright, and top is the hypothesis. A left pair is obtained from the top-membership clause when top belongs to the set, and from the left half of a both-projections derivation by the projection clause, using the same statement recursively. A right pair is obtained symmetrically from the right half.
ai-/
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
