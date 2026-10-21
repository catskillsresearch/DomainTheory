/-ai
An approximable mapping, in the sense of Definition 5.1 of Scott 1982, from an information system A to an information system B is a relation between finite sets of tokens such that related sets are consistent, the empty sets are related, the relation is closed under union on the right, and it is monotone for entailment of A on the left and entailment of B on the right.
ai-/
module


public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35

@[expose] public section

universe u v

namespace DomainTheory.InformationSystems
namespace InfoSys

open DomainTheory.InformationSystems.Constructive

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- **Definition 5.1 (Scott 1982).** Approximable mapping between information systems. -/
structure ApproximableMap (A : InfoSys α) (B : InfoSys β) where
  rel : Finset α → Finset β → Prop
  rel_dom : ∀ {u v}, rel u v → u ∈ A.Con
  rel_cod : ∀ {u v}, rel u v → v ∈ B.Con
  empty_rel : rel ∅ ∅
  union_right : ∀ {u v v'}, rel u v → rel u v' → rel u (v ∪' v')
  mono : ∀ {u u' v v'},
    rel u v → A.EntSet u' u → B.EntSet v v' → u' ∈ A.Con → v' ∈ B.Con → rel u' v'

end InfoSys
end DomainTheory.InformationSystems
