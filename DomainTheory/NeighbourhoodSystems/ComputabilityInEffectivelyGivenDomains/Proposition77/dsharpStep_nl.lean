module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharpStep_nl (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 2) (2 * b + 1)) tbl) = packT 0 0 0 := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 2) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 1) = 0 by omega, selectFn_zero,
    show (2 * a + 2) % 2 = 0 by omega, selectFn_zero,
    show (2 * b + 1) % 2 = 1 by omega, selectFn_one]

end Proposition77

end DomainTheory.NeighbourhoodSystems
