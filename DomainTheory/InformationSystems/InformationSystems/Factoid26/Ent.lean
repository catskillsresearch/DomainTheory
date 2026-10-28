module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Consistent

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid26

def Ent {A B : Type*} (u : Finset (Token A B)) (X : Token A B) : Prop :=
  Consistent u ∧ (X = Token.bot ∨ X ∈ u)

end Factoid26

end DomainTheory.InformationSystems
