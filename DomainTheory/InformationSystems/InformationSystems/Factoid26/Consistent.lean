/-ai
A finite set of tokens is consistent when any two graph atoms in the set that share a first component have equal second components. The condition quantifies only over graph atoms.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid26

/-- Scott’s consistency: the pairs in `u` form a partial function `A ⇀ B`
(`bot` is ignored). -/
def Consistent {A B : Type*} (u : Finset (Token A B)) : Prop :=
  ∀ ⦃a : A⦄ ⦃b b' : B⦄,
    Token.pair a b ∈ u → Token.pair a b' ∈ u → b = b'

end Factoid26

end DomainTheory.InformationSystems
