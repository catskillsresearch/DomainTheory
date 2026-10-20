module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Payload of tree entailment (Scott §8 (8)–(12)), recursive on the token.

The extra disjuncts for `pairL bot` / `pairR bot` match official product
`ent_bot`: any nonempty pair-set entails the unique product bottom, which
`treeUnfold` identifies as both constructors. Without them, closed tree
elements could contain one encoding of `(Δ,Δ)` but not the other, and
`|T|` would fail to be order-isomorphic to `|A + (T × T)|`. -/
def TreeEntPayload (u : Finset (TreeToken α)) : TreeToken α → Prop
  | .bot => True
  | .atom x => atomFinset u ≠ ∅ ∧ A.Ent (atomFinset u) x
  | .pairL t =>
      atomFinset u = ∅ ∧ TreeCon A (pairLFinset u) ∧ TreeCon A (pairRFinset u) ∧
        ((pairLFinset u ≠ ∅ ∧ TreeEntPayload (pairLFinset u) t) ∨
          (t = .bot ∧ pairRFinset u ≠ ∅))
  | .pairR t =>
      atomFinset u = ∅ ∧ TreeCon A (pairRFinset u) ∧ TreeCon A (pairLFinset u) ∧
        ((pairRFinset u ≠ ∅ ∧ TreeEntPayload (pairRFinset u) t) ∨
          (t = .bot ∧ pairLFinset u ≠ ∅))

end InfoSys

end DomainTheory.InformationSystems
