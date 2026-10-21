/-ai
The stage-n approximation of an infinite binary path is the finite element of the length-n prefix of the path.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_length

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- The finite approximations `σₙ⊥ = (p ↾ n)⊥` along the path `p`. -/
def branchSeq (p : ℕ → Bool) (n : ℕ) : B.Element := sigmaBot (prefixSeq p n)

end DomainTheory.NeighbourhoodSystems.Exercise113
