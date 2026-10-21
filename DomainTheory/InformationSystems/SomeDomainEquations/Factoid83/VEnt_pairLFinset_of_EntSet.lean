/-ai
If every member of u is V-entailed by v, then either top belongs to v, or every member of the left pair projection of u is V-entailed by the left pair projection of v. This pushes an entailment set through the left projection, or absorbs it through top.

If top belongs to v, take the first alternative. Otherwise a member of the left projection of u comes from a left pair in u, which v entails. Inverting that entailment, top cannot belong to v, so the left projection of v entails the member.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_pairL_inv

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- Push an `EntSet` through the left projection (or absorb via top). -/
theorem VEnt_pairLFinset_of_EntSet {u v : Finset VToken}
    (hEnts : ∀ y ∈ u, VEnt v y) :
    .top ∈ v ∨ (∀ y ∈ vPairLFinset u, VEnt (vPairLFinset v) y) := by
  by_cases htop : .top ∈ v
  · exact Or.inl htop
  · refine Or.inr ?_
    intro y hy
    have hy' := hEnts _ (mem_vPairLFinset.1 hy)
    rcases VEnt_pairL_inv hy' with hm | hproj
    · exact False.elim (htop hm)
    · exact hproj

end InfoSys

end DomainTheory.InformationSystems
