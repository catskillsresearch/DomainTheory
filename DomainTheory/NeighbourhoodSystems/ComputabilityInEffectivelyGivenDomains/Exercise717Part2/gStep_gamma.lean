/-ai
On the code of zero paired with a certificate, and on any memo table, the certificate step returns the pair of the master guard on the certificate's output component and the master index, with that output component.

Unpairing selects the zero branch of the first selector, which returns that pair.
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


theorem gStep_gamma (cert tbl : ℕ) :
    gStep fe fU fV mIdx (Nat.pair (Nat.pair 0 cert) tbl)
      = Nat.pair (fe (Nat.pair cert.unpair.1 mIdx)) cert.unpair.1 := by
  simp only [gStep, unpair_pair_fst, unpair_pair_snd, Nat.sub_zero, selectFn_one]

end Computability
end Exercise717
end DomainTheory.NeighbourhoodSystems
