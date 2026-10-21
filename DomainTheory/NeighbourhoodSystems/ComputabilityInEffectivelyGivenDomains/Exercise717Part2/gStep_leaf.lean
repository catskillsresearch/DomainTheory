/-ai
On an odd code two times a plus one, paired with a certificate, the certificate step returns the pair of the leaf guard on the certificate's witness, a, and the output component, with that output component.

The first selector sees a positive code and takes its second branch. The second selector sees remainder one and takes its first branch, and division by two recovers a.
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
