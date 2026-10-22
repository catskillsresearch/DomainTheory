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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.encodeDeltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.digit_add_mul_pow_of_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.digit_eq_of_encodeDeltaPair

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **The inversion property**: `deltaPair (encodeDeltaPair δ n)` agrees with `δ` on every position
strictly below `n`. Combined with `atomPairG_congr` (`(d)(1)`, already `Pass`), this is exactly
what transports `(c)(ii)`'s `Fin n → Bool × Bool`-indexed classical covering fact into the
`deltaPair`/bit-source-indexed one `XPseqCode`'s fold actually uses (`atomPairG_master_covered_deltaPair`
below). -/
theorem deltaPair_encodeDeltaPair (δ : ℕ → Bool × Bool) :
    ∀ n i, i < n → deltaPair (encodeDeltaPair δ n) i = δ i := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · show (decide ((encodeDeltaPair δ (n + 1) / 4 ^ i) % 2 = 1),
          decide ((encodeDeltaPair δ (n + 1) / 4 ^ i / 2) % 2 = 1)) = δ i
      have key : encodeDeltaPair δ (n + 1) / 4 ^ i % 4 = encodeDeltaPair δ n / 4 ^ i % 4 := by
        show (encodeDeltaPair δ n +
          ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n) / 4 ^ i % 4 = _
        exact digit_add_mul_pow_of_lt _ _ _ _ hi'
      have h1 : (encodeDeltaPair δ (n + 1) / 4 ^ i) % 2 =
          (encodeDeltaPair δ n / 4 ^ i) % 2 := by omega
      have h2 : (encodeDeltaPair δ (n + 1) / 4 ^ i / 2) % 2 =
          (encodeDeltaPair δ n / 4 ^ i / 2) % 2 := by omega
      rw [h1, h2]
      show (decide ((encodeDeltaPair δ n / 4 ^ i) % 2 = 1),
          decide ((encodeDeltaPair δ n / 4 ^ i / 2) % 2 = 1)) = δ i
      exact ih i hi'
    · have hd := digit_eq_of_encodeDeltaPair δ i
      show (decide ((encodeDeltaPair δ (i + 1) / 4 ^ i) % 2 = 1),
          decide ((encodeDeltaPair δ (i + 1) / 4 ^ i / 2) % 2 = 1)) = δ i
      rw [hd]
      rcases Bool.eq_false_or_eq_true (δ i).1 with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (δ i).2 with h2 | h2 <;>
        simp [h1, h2, Prod.ext_iff]

end DomainTheory.NeighbourhoodSystems
