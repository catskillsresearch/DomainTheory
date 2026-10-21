/-ai
From an entailment of a left pair (X, Δ), either top belongs to the premise or the left pair projection of the premise entails X.

Case analysis on the derivation gives the first alternative from the top-membership clause and the second from the projection clause.
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

/-- From `v ⊢ (X, Δ)`, either `∇ ∈ v` or the left projection entails `X`. -/
theorem VEnt_pairL_inv {v : Finset VToken} {x : VToken}
    (h : VEnt v (.pairL x)) : .top ∈ v ∨ VEnt (vPairLFinset v) x := by
  cases h with
  | pairL_top hm => exact Or.inl hm
  | pairL_proj h' => exact Or.inr h'

end InfoSys

end DomainTheory.InformationSystems
