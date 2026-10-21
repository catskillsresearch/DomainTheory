/-ai
The empty set of V-tokens does not entail top, because no derivation of top bottoms out at the empty set.

A stronger statement is proved: an entailment of top never has empty premise. Induct on the derivation. A bottom, left-pair, or right-pair conclusion is distinct from top. Membership of top cannot occur in the empty set. A both-projections derivation of top from the empty set would yield a top-entailment from the left projection, and that projection of the empty set is empty. The claim is this statement for the empty set and top.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset_empty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- Empty set does not entail top (no derivation bottoms out). -/
theorem not_VEnt_empty_top : ¬ VEnt (∅ : Finset VToken) .top := by
  have aux : ∀ {u : Finset VToken} {c : VToken},
      VEnt u c → c = .top → u = ∅ → False := by
    intro u c h
    induction h with
    | bot => intro hc; exact nomatch hc
    | top_mem hm =>
      intro _ hu; exact Finset.notMem_empty _ (hu ▸ hm)
    | top_both _ _ ihL _ =>
      intro _ hu
      exact ihL rfl (by rw [hu]; exact vPairLFinset_empty)
    | pairL_top => intro hc; exact nomatch hc
    | pairL_proj => intro hc; exact nomatch hc
    | pairR_top => intro hc; exact nomatch hc
    | pairR_proj => intro hc; exact nomatch hc
  exact fun h => aux h rfl rfl

end InfoSys

end DomainTheory.InformationSystems
