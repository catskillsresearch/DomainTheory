/-ai
The first component of the second component of the second component of a code is at most the code.

Each unpairing of a first or second component does not increase the code, and the three inequalities compose.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}
















/-- A decoded sub-component is `≤` the code it is decoded from. -/
theorem unpair_snd_snd_fst_le (c : ℕ) : c.unpair.2.unpair.2.unpair.1 ≤ c := by
  have h1 := unpair_snd_le c
  have h2 := unpair_snd_le c.unpair.2
  have h3 := unpair_fst_le c.unpair.2.unpair.2
  omega

end Exercise717
end DomainTheory.NeighbourhoodSystems
