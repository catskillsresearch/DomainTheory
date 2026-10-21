/-ai
The digit just written by encodeDeltaPair at position n is recovered by dividing the successor encoding by four to the n.

Expand the successor. Division by four to the n separates the previous encoding, which is strictly smaller than that power and contributes zero, from the new digit.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.encodeDeltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.encodeDeltaPair_lt

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- `encodeDeltaPair`'s freshly-added digit at position `n` is read straight back off by dividing
out the lower `4 ^ n` (which is exactly `encodeDeltaPair δ n`, `< 4 ^ n` by `encodeDeltaPair_lt`,
hence contributes `0` to the quotient). -/
theorem digit_eq_of_encodeDeltaPair (δ : ℕ → Bool × Bool) (n : ℕ) :
    encodeDeltaPair δ (n + 1) / 4 ^ n =
      (if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0) := by
  show (encodeDeltaPair δ n +
      ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n) / 4 ^ n = _
  rw [Nat.add_mul_div_right _ _ (pow_pos (by norm_num) n),
    Nat.div_eq_of_lt (encodeDeltaPair_lt δ n), Nat.zero_add]

end DomainTheory.NeighbourhoodSystems
