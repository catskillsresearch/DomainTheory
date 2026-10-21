/-ai
A token of the bottom element is entailed by the empty set.

Entailment transitivity is applied to the fact that every token of the singleton bottom token is the bottom token, which the empty set entails, together with membership in the bottom element.
ai-/
module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem mem_botElement_emptyEntails (A : InfoSys α) {X : α}
    (h : X ∈ A.botElement.carrier) : A.Ent (∅ : Finset α) X :=
  A.ent_trans A.con_empty (A.con_sing A.bot)
    (fun x hx => by
      have : x = A.bot := Finset.mem_singleton.mp hx
      subst this
      exact A.ent_bot A.con_empty)
    h

end InfoSys

end DomainTheory.InformationSystems
