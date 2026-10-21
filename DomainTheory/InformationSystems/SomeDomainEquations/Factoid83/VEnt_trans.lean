/-ai
V-entailment is transitive: if every member of u is entailed by v and u entails c, then v entails c.

Induct on the derivation of the entailment from u. Bottom is entailed outright. Membership of top is the given entailment of that member by v. For a both-projections derivation, push the entailment set through the left projection. If top belongs to v, then v entails top by the rogue-top property; otherwise push through the right projection in the same way. If neither side meets top, the inductive hypotheses supply both projection entailments. A left pair derived from membership of top is the rogue-top consequence of the entailment of that member. A left pair derived by projection either finds top in v, giving the top-membership clause, or passes the projected entailment set to the inductive hypothesis. The two right-pair cases are symmetric.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_of_ent_top
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_pairLFinset_of_EntSet
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_pairRFinset_of_EntSet

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem VEnt_trans {u v : Finset VToken} {c : VToken}
    (hEnts : ∀ y ∈ u, VEnt v y) (h : VEnt u c) : VEnt v c := by
  induction h generalizing v with
  | bot => exact VEnt.bot
  | top_mem hm => exact hEnts _ hm
  | top_both _ _ ihL ihR =>
    rcases VEnt_pairLFinset_of_EntSet hEnts with hm | hL
    · exact VEnt_of_ent_top (VEnt.top_mem hm) .top
    · rcases VEnt_pairRFinset_of_EntSet hEnts with hm | hR
      · exact VEnt_of_ent_top (VEnt.top_mem hm) .top
      · exact VEnt.top_both (ihL hL) (ihR hR)
  | pairL_top hm => exact VEnt_of_ent_top (hEnts _ hm) _
  | pairL_proj _ ih =>
    rcases VEnt_pairLFinset_of_EntSet hEnts with hm | hL
    · exact VEnt.pairL_top hm
    · exact VEnt.pairL_proj (ih hL)
  | pairR_top hm => exact VEnt_of_ent_top (hEnts _ hm) _
  | pairR_proj _ ih =>
    rcases VEnt_pairRFinset_of_EntSet hEnts with hm | hR
    · exact VEnt.pairR_top hm
    · exact VEnt.pairR_proj (ih hR)

end InfoSys

end DomainTheory.InformationSystems
