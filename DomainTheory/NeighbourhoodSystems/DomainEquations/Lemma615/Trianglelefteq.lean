/-ai
A neighbourhood system D embeds as a subdomain of a neighbourhood system E when some neighbourhood system on the token type of E is a subdomain of E and is isomorphic to D.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Scott's `⊴` (the prose before Lemma 6.15).** `D ⊴ E` means `D ≅ D'` for some subdomain
`D' ◁ E`: `D` *embeds as a subdomain* of `E`. -/
def Trianglelefteq (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) : Prop :=
  ∃ D' : NeighborhoodSystem β, D' ◁ E ∧ (D ≅ᴰ D')

end DomainTheory.NeighbourhoodSystems
