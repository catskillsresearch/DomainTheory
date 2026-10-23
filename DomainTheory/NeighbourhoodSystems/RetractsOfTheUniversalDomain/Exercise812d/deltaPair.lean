module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.digit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **The two-bits-per-depth sign sequence** read off a bit-source `k`, the `atomPairG`-shaped
analogue of `Theorem88d.lean`'s `deltaOf`: the depth-`i` nibble `(k / 4 ^ i) % 2` supplies `(δ i).1`,
and `(k / 4 ^ i / 2) % 2` supplies `(δ i).2` — matching exactly how `atomPairStep` peels two bits
per depth from `rem` (`rem % 2`, `(rem / 2) % 2`, then `rem / 4`). -/
def deltaPair (k : ℕ) : ℕ → Bool × Bool :=
  fun i => (decide ((k / 4 ^ i) % 2 = 1), decide ((k / 4 ^ i / 2) % 2 = 1))

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace deltaPair

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem fst_eq_testBit (k i : ℕ) : (deltaPair k i).1 = k.testBit (2 * i) := by
  show decide ((k / 4 ^ i) % 2 = 1) = k.testBit (2 * i)
  rw [Nat.testBit_eq_decide_div_mod_eq, show (4 : ℕ) ^ i = 2 ^ (2 * i) by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]]

end deltaPair
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace deltaPair

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem snd_eq_testBit (k i : ℕ) : (deltaPair k i).2 = k.testBit (2 * i + 1) := by
  show decide ((k / 4 ^ i / 2) % 2 = 1) = k.testBit (2 * i + 1)
  rw [Nat.div_div_eq_div_mul, Nat.testBit_eq_decide_div_mod_eq, show (4 : ℕ) ^ i * 2 = 2 ^ (2 * i + 1)
    by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, pow_succ]]

end deltaPair
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace deltaPair

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **The inversion property**: `deltaPair (encodeDeltaPair δ n)` agrees with `δ` on every position
strictly below `n`. Combined with `atomPairG.congr` (`(d)(1)`, already `Pass`), this is exactly
what transports `(c)(ii)`'s `Fin n → Bool × Bool`-indexed classical covering fact into the
`deltaPair`/bit-source-indexed one `XPseqCode`'s fold actually uses (`atomPairG.master_covered_deltaPair`
below). -/
theorem encodeDeltaPair (δ : ℕ → Bool × Bool) :
    ∀ n i, i < n → deltaPair (_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n) i = δ i := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · show (decide ((_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i) % 2 = 1),
          decide ((_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i / 2) % 2 = 1)) = δ i
      have key : _root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i % 4 = _root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i % 4 := by
        show (_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n +
          ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n) / 4 ^ i % 4 = _
        exact digit.add_mul_pow_of_lt _ _ _ _ hi'
      have h1 : (_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i) % 2 =
          (_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i) % 2 := by omega
      have h2 : (_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (n + 1) / 4 ^ i / 2) % 2 =
          (_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i / 2) % 2 := by omega
      rw [h1, h2]
      show (decide ((_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i) % 2 = 1),
          decide ((_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ n / 4 ^ i / 2) % 2 = 1)) = δ i
      exact ih i hi'
    · have hd := digit.eq_of_encodeDeltaPair δ i
      show (decide ((_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (i + 1) / 4 ^ i) % 2 = 1),
          decide ((_root_.DomainTheory.NeighbourhoodSystems.encodeDeltaPair δ (i + 1) / 4 ^ i / 2) % 2 = 1)) = δ i
      rw [hd]
      rcases Bool.eq_false_or_eq_true (δ i).1 with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (δ i).2 with h2 | h2 <;>
        simp [h1, h2, Prod.ext_iff]

end deltaPair
end DomainTheory.NeighbourhoodSystems
