/-ai
If the tag of a natural-number code is positive, then its payload is strictly smaller than the code.

The payload is at most the code formed by pairing zero with the payload. That code is strictly smaller than the code formed by pairing the positive tag with the payload. Restoring the original code by cancellation of packing, and combining the two comparisons, gives the strict inequality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TermAlgebra

/-- If `c`'s tag (`c.unpair.1`) is nonzero, `c`'s payload (`c.unpair.2`) is *strictly* smaller than
`c` itself — the key well-foundedness fact driving `nodeCode`'s children being strictly smaller
than the parent (choice-free: only uses the custom `unpair_pair`/`le_pair_right`/
`Nat.pair_lt_pair_left`, all already audited elsewhere in this file). -/
theorem unpair_snd_lt_of_unpair_fst_pos {c : ℕ} (h : 0 < c.unpair.1) : c.unpair.2 < c := by
  have h1 : c.unpair.2 ≤ Nat.pair 0 c.unpair.2 := le_pair_right 0 c.unpair.2
  have h2 : Nat.pair 0 c.unpair.2 < Nat.pair c.unpair.1 c.unpair.2 := Nat.pair_lt_pair_left _ h
  rw [Nat.pair_unpair] at h2
  omega

end TermAlgebra

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
