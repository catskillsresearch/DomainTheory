/-ai
Consistency of a finite set of tree tokens, in the sense of Scott's clauses (4) through (7), is defined inductively by two clauses. The set is left-consistent when its atom projection is consistent in the atom information system and both pair projections are empty. The set is right-consistent when its atom projection is empty and both pair projections are themselves consistent.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

/-- Consistency for trees (Scott §8 (4)–(7)). -/
inductive TreeCon : Finset (TreeToken α) → Prop where
  | left (u : Finset (TreeToken α))
      (hA : atomFinset u ∈ A.Con)
      (hL : pairLFinset u = ∅) (hR : pairRFinset u = ∅) : TreeCon u
  | right (u : Finset (TreeToken α))
      (hA : atomFinset u = ∅)
      (hL : TreeCon (pairLFinset u)) (hR : TreeCon (pairRFinset u)) : TreeCon u

end InfoSys
end DomainTheory.InformationSystems
