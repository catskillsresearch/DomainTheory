/-ai
The entailment payload of a finite set of tree tokens, in the sense of Scott's clauses (8) through (12), is defined by recursion on the token. The bottom token is always in the payload. An atom is in the payload when the atom projection is nonempty and the atom information system entails that atom from the atom projection. A left-pair token is in the payload when the atom projection is empty, both pair projections are consistent, and either the left pair projection is nonempty and carries the payload of the inner token, or the inner token is the bottom and the right pair projection is nonempty. A right-pair token is described symmetrically. The two bottom disjuncts record that any nonempty pair projection entails the bottom, matching the product bottom axiom, since the unfolding identifies both pair-bottom constructors with the single product bottom.
ai-/
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
