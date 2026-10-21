/-ai
A finite set entails a token when the set is consistent and the token is either the least-informative token or a member of the set.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Consistent

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid26

/-- Minimal entailment, with LHS consistency baked in (Scott types `⊢` on `Con`). -/
def Ent {A B : Type*} (u : Finset (Token A B)) (X : Token A B) : Prop :=
  Consistent u ∧ (X = Token.bot ∨ X ∈ u)

end Factoid26

end DomainTheory.InformationSystems
