/-ai
diffNFA is the automaton whose states are pairs of finite sets of states of two expressions. Its step and its start are singletons, advancing each component by the finite step from the pair of finite start sets, and a pair is accepting when the first component meets the accept set of the first expression and the second component is disjoint from the accept set of the second expression.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.acceptFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.startFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.stepFin

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

/-- Tracks `(evalFin e₁ w, evalFin e₂ w)` deterministically; accepts `w` iff `e₁` is live-accepting
and `e₂` is not — i.e. `w ∈ denote e₁ \ denote e₂`. -/
def diffNFA (e1 e2 : SExpr) : NFA Bool (Finset (autState e1) × Finset (autState e2)) where
  step S c := {(stepFin e1 S.1 c, stepFin e2 S.2 c)}
  start := {(startFin e1, startFin e2)}
  accept := {S | (S.1 ∩ acceptFin e1).Nonempty ∧ S.2 ∩ acceptFin e2 = ∅}

end Exercise722

end DomainTheory.NeighbourhoodSystems
