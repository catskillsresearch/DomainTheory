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

















section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


theorem gStep_leaf (a cert tbl : ℕ) :
    gStep fe fU fV mIdx (Nat.pair (Nat.pair (2 * a + 1) cert) tbl)
      = Nat.pair (fU (Nat.pair cert.unpair.2.unpair.1 (Nat.pair a cert.unpair.1)))
          cert.unpair.1 := by
  simp only [gStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 1) = 0 by omega, selectFn_zero,
    show (2 * a + 1) % 2 = 1 by omega, selectFn_one, show (2 * a + 1) / 2 = a by omega]

end Computability
end Exercise717
end DomainTheory.NeighbourhoodSystems
