module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- Adding a higher digit (`d * 4 ^ n`, `n > i`) never disturbs a `deltaPair`-digit strictly
below `n`. The purely-arithmetic core making `encodeDeltaPair`'s induction go through. -/
theorem digit_add_mul_pow_of_lt (m d i n : ℕ) (hi : i < n) :
    (m + d * 4 ^ n) / 4 ^ i % 4 = m / 4 ^ i % 4 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have heq : d * 4 ^ (i + j + 1) = 4 ^ i * (4 * 4 ^ j * d) := by ring
  rw [heq, Nat.add_mul_div_left m _ (pow_pos (by norm_num) i)]
  rw [show 4 * 4 ^ j * d = 4 * (4 ^ j * d) by ring]
  exact Nat.add_mul_mod_self_left _ _ _

end DomainTheory.NeighbourhoodSystems
