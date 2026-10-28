module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem VEnt_insert_top_imp {u : Finset VToken} {y : VToken}
    (hy : y ≠ .top) (hEnt : VEnt u y) (hIns : VEnt (insert y u) .top) :
    VEnt u .top := by
  induction y generalizing u with
  | bot =>
    cases hIns with
    | top_mem hm =>
      rcases Finset.mem_insert.mp hm with h | h
      · exact False.elim (nomatch h)
      · exact VEnt.top_mem h
    | top_both hL hR =>
      rw [vPairLFinset_insert_bot] at hL
      rw [vPairRFinset_insert_bot] at hR
      exact VEnt.top_both hL hR
  | top => exact False.elim (hy rfl)
  | pairL x ih =>
    cases hIns with
    | top_mem hm =>
      rcases Finset.mem_insert.mp hm with h | h
      · exact False.elim (nomatch h)
      · exact VEnt.top_mem h
    | top_both hL hR =>
      rw [vPairLFinset_insert_pairL] at hL
      rw [vPairRFinset_insert_pairL] at hR
      rcases VEnt.pairL_inv hEnt with htop | hx
      · exact VEnt.top_mem htop
      · by_cases hxTop : x = .top
        · subst hxTop; exact VEnt.top_both hx hR
        · exact VEnt.top_both (ih hxTop hx hL) hR
  | pairR z ih =>
    cases hIns with
    | top_mem hm =>
      rcases Finset.mem_insert.mp hm with h | h
      · exact False.elim (nomatch h)
      · exact VEnt.top_mem h
    | top_both hL hR =>
      rw [vPairLFinset_insert_pairR] at hL
      rw [vPairRFinset_insert_pairR] at hR
      rcases VEnt.pairR_inv hEnt with htop | hz
      · exact VEnt.top_mem htop
      · by_cases hzTop : z = .top
        · subst hzTop; exact VEnt.top_both hL hz
        · exact VEnt.top_both hL (ih hzTop hz hR)

end InfoSys

end DomainTheory.InformationSystems
