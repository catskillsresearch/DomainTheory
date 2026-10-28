module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid26

def Consistent {A B : Type*} (u : Finset (Token A B)) : Prop :=
  ∀ ⦃a : A⦄ ⦃b b' : B⦄,
    Token.pair a b ∈ u → Token.pair a b' ∈ u → b = b'

end Factoid26

end DomainTheory.InformationSystems
