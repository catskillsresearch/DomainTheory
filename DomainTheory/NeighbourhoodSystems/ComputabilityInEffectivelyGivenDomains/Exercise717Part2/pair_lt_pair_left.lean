/-ai
Numerical pairing is strictly monotone in its first argument when the second argument is held fixed.

The definition of pairing is unfolded, and the comparisons with the fixed second argument are split. If both first arguments lie below it, the inequality is the given comparison. If only the smaller one does, the square of the larger first argument dominates the square of the second argument. If neither does, the square of the successor of the smaller first argument is at most the square of the larger, and expanding that square leaves room for the strict inequality.
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
















/-- `Nat.pair` is strictly monotone in its first argument (second argument fixed). -/
theorem pair_lt_pair_left {a c b : ℕ} (h : a < c) : Nat.pair a b < Nat.pair c b := by
  unfold Nat.pair
  rcases Nat.lt_or_ge a b with hab | hab
  · rw [ite_eq_left hab]
    rcases Nat.lt_or_ge c b with hcb | hcb
    · rw [ite_eq_left hcb]; omega
    · rw [ite_eq_right (Nat.not_lt.mpr hcb)]
      have hbc : b * b ≤ c * c := Nat.mul_le_mul hcb hcb
      omega
  · rw [ite_eq_right (Nat.not_lt.mpr hab),
      ite_eq_right (Nat.not_lt.mpr (le_of_lt (lt_of_le_of_lt hab h)))]
    have hcc : (a + 1) * (a + 1) ≤ c * c := Nat.mul_le_mul h h
    have hexp : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
    omega

end Exercise717
end DomainTheory.NeighbourhoodSystems
