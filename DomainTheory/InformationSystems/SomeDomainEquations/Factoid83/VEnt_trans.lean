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
