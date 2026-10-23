module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace digit

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- Adding a higher digit (`d * 4 ^ n`, `n > i`) never disturbs a `deltaPair`-digit strictly
below `n`. The purely-arithmetic core making `encodeDeltaPair`'s induction go through. -/
theorem add_mul_pow_of_lt (m d i n : ℕ) (hi : i < n) :
    (m + d * 4 ^ n) / 4 ^ i % 4 = m / 4 ^ i % 4 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have heq : d * 4 ^ (i + j + 1) = 4 ^ i * (4 * 4 ^ j * d) := by ring
  rw [heq, Nat.add_mul_div_left m _ (pow_pos (by norm_num) i)]
  rw [show 4 * 4 ^ j * d = 4 * (4 ^ j * d) by ring]
  exact Nat.add_mul_mod_self_left _ _ _

end digit
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace digit

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- `encodeDeltaPair`'s freshly-added digit at position `n` is read straight back off by dividing
out the lower `4 ^ n` (which is exactly `encodeDeltaPair δ n`, `< 4 ^ n` by `encodeDeltaPair_lt`,
hence contributes `0` to the quotient). -/
theorem eq_of_encodeDeltaPair (δ : ℕ → Bool × Bool) (n : ℕ) :
    encodeDeltaPair δ (n + 1) / 4 ^ n =
      (if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0) := by
  show (encodeDeltaPair δ n +
      ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n) / 4 ^ n = _
  rw [Nat.add_mul_div_right _ _ (pow_pos (by norm_num) n),
    Nat.div_eq_of_lt (encodeDeltaPair_lt δ n), Nat.zero_add]

end digit
end DomainTheory.NeighbourhoodSystems
