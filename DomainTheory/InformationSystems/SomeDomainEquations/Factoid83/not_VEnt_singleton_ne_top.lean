/-ai
The singleton of a token other than top does not entail top.

Match the token against the derivation. If the token is bottom, it is distinct from a member equal to top, and a both-projections derivation has empty left projection, which does not entail top. The case of the top token contradicts the hypothesis. If the token is a left pair, it is distinct from a member equal to top, and a both-projections derivation has empty right projection, which does not entail top. If the token is a right pair, the left projection of the singleton is empty, and the same emptiness fact applies.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.not_VEnt_empty_top
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- Singleton of a non-top token does not entail top. -/
theorem not_VEnt_singleton_ne_top {t : VToken} (ht : t ≠ .top) :
    ¬ VEnt ({t} : Finset VToken) .top := by
  intro h
  match t, h with
  | .bot, .top_mem hm =>
    exact False.elim (nomatch Finset.mem_singleton.mp hm)
  | .bot, .top_both hL _ =>
    have hL' : vPairLFinset ({.bot} : Finset VToken) = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch mem_vPairLFinset.1 hx)
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    exact not_VEnt_empty_top (by rwa [hL'] at hL)
  | .top, _ => exact ht rfl
  | .pairL x, .top_mem hm =>
    exact False.elim (nomatch Finset.mem_singleton.mp hm)
  | .pairL x, .top_both _ hR =>
    have hR' : vPairRFinset ({.pairL x} : Finset VToken) = ∅ := by
      ext y; constructor
      · intro hy; exact False.elim (nomatch mem_vPairRFinset.1 hy)
      · intro hy; exact False.elim (Finset.notMem_empty y hy)
    exact not_VEnt_empty_top (by rwa [hR'] at hR)
  | .pairR y, .top_mem hm =>
    exact False.elim (nomatch Finset.mem_singleton.mp hm)
  | .pairR y, .top_both hL _ =>
    have hL' : vPairLFinset ({.pairR y} : Finset VToken) = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch mem_vPairLFinset.1 hx)
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    exact not_VEnt_empty_top (by rwa [hL'] at hL)

end InfoSys

end DomainTheory.InformationSystems
