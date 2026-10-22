module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharpStep_nn (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 2) (2 * b + 2)) tbl)
      = packT
          (eqB (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.1 b.unpair.1))
            * eqB (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.2 b.unpair.2)))
          (consB (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.1 b.unpair.1))
            * consB (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.2 b.unpair.2)))
          (2 * Nat.pair
            (intI (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.1 b.unpair.1)))
            (intI (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.2 b.unpair.2)))
            + 2) := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 2) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 2) = 0 by omega, selectFn_zero,
    show (2 * a + 2) % 2 = 0 by omega, selectFn_zero,
    show (2 * b + 2) % 2 = 0 by omega, selectFn_zero,
    show (2 * a + 2) / 2 - 1 = a by omega, show (2 * b + 2) / 2 - 1 = b by omega]

end Proposition77

end DomainTheory.NeighbourhoodSystems
