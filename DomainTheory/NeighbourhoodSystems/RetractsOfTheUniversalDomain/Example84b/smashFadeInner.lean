/-ai
The inner application of Scott's smash is the approximable map on the product sending z to fade of the pair consisting of check of the second coordinate and z itself. It is fade on the product, composed with the pairing of check after the second projection and the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_fst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_snd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash

/-- The inner application `fade(check(y), z)` of Scott's `smash(x, y) = fade(check(x),
fade(check(y), ⟨x, y⟩))`: here `z = ⟨x, y⟩` is passed through `idMap` (Scott's `⟨x,y⟩` *is* the
ambient input). -/
def smashFadeInner : ApproximableMap (prod D E) (prod D E) :=
  (fade (D := prod D E)).comp
    (paired ((check (D := E)).comp (proj₁ D E)) (idMap (prod D E)))

end Smash

end DomainTheory.NeighbourhoodSystems
