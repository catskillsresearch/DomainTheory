/-ai
The length-n initial segment of an infinite path of bits is the empty list when n is zero, and at a successor it is the previous segment with the next bit of the path appended.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- The length-`n` initial segment `p ↾ n = ⟨p 0, …, p (n-1)⟩` of an infinite path `p`. -/
def prefixSeq (p : ℕ → Bool) : ℕ → Str
  | 0 => []
  | (n + 1) => prefixSeq p n ++ [p n]

end DomainTheory.NeighbourhoodSystems.Exercise113
