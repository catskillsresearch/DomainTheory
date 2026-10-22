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


/-- `Nat.pair` is monotone in its second argument (first argument fixed). -/
theorem pair_le_pair_right {a b d : ℕ} (h : b ≤ d) : Nat.pair a b ≤ Nat.pair a d := by
  unfold Nat.pair
  rcases Nat.lt_or_ge a b with hab | hab
  · rw [ite_eq_left hab, ite_eq_left (lt_of_lt_of_le hab h)]
    have : b * b ≤ d * d := Nat.mul_le_mul h h
    omega
  · rw [ite_eq_right (Nat.not_lt.mpr hab)]
    rcases Nat.lt_or_ge a d with had | had
    · rw [ite_eq_left had]
      have h1 : a * a + a ≤ d * d := by
        calc a * a + a = a * (a + 1) := by ring
          _ ≤ a * d := Nat.mul_le_mul (le_refl a) had
          _ ≤ d * d := Nat.mul_le_mul had.le (le_refl d)
      omega
    · rw [ite_eq_right (Nat.not_lt.mpr had)]; omega

end Exercise717
end DomainTheory.NeighbourhoodSystems
