module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myDivPow2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem myDivPow2_eq (m ℓ : ℕ) : myDivPow2 m ℓ = m / 2 ^ ℓ := by
  unfold myDivPow2
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    show (ℓ.rec m (fun _ ih => ih / 2)) / 2 = m / 2 ^ (ℓ + 1)
    rw [ih, Nat.div_div_eq_div_mul, ← pow_succ]

end DomainTheory.NeighbourhoodSystems
