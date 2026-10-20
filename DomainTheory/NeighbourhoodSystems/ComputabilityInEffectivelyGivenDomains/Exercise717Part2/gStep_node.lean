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


theorem gStep_node (a cert tbl : ℕ) :
    gStep fe fU fV mIdx (Nat.pair (Nat.pair (2 * a + 2) cert) tbl)
      = Nat.pair
          ((listGet tbl (Nat.pair (2 * a + 2) cert - 1
                - Nat.pair a.unpair.1 cert.unpair.2.unpair.2.unpair.1)).unpair.1
            * (listGet tbl (Nat.pair (2 * a + 2) cert - 1
                - Nat.pair a.unpair.2 cert.unpair.2.unpair.2.unpair.2)).unpair.1
            * fV (Nat.pair cert.unpair.2.unpair.1
                (Nat.pair (Nat.pair
                    (listGet tbl (Nat.pair (2 * a + 2) cert - 1
                      - Nat.pair a.unpair.1 cert.unpair.2.unpair.2.unpair.1)).unpair.2
                    (listGet tbl (Nat.pair (2 * a + 2) cert - 1
                      - Nat.pair a.unpair.2 cert.unpair.2.unpair.2.unpair.2)).unpair.2)
                  cert.unpair.1)))
          cert.unpair.1 := by
  simp only [gStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 2) = 0 by omega, selectFn_zero,
    show (2 * a + 2) % 2 = 0 by omega, selectFn_zero, show (2 * a + 2) / 2 - 1 = a by omega]

end Computability
end Exercise717
end DomainTheory.NeighbourhoodSystems
