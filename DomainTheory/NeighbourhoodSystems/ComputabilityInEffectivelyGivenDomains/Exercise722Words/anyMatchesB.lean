/-ai
The Boolean anyMatchesB e ws is true when some word of the finite list ws is accepted by the matcher matchesB e. It is the list quantifier any applied to that matcher. Evaluating it on sigma and wordsUpTo 0 is the example that should return true, because the empty word lies in sigma.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public meta import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words.wordsUpTo

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- True iff some word in `ws` is accepted by `matchesB e`. -/
def anyMatchesB (e : SExpr) (ws : List (List Bool)) : Bool := ws.any (matchesB e)

#eval anyMatchesB .sigma (wordsUpTo 0) -- should be `true` (the empty word lies in Σ)

end Exercise722

end DomainTheory.NeighbourhoodSystems
