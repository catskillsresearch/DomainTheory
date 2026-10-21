/-ai
If the first argument of a numerical pair strictly increases and the second argument does not decrease, then the pair strictly increases.

Strict increase in the first argument, with the second held at the smaller value, is combined with weak increase in the second argument, with the first held at the larger value.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.pair_lt_pair_left
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.pair_le_pair_right

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}
















/-- Combined: strict in the first argument, monotone in the second. -/
theorem pair_lt_pair_of_lt_le {a c b d : ℕ} (hac : a < c) (hbd : b ≤ d) :
    Nat.pair a b < Nat.pair c d :=
  lt_of_lt_of_le (pair_lt_pair_left hac) (pair_le_pair_right hbd)

end Exercise717
end DomainTheory.NeighbourhoodSystems
