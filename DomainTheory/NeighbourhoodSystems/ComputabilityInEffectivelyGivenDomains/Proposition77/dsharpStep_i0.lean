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

theorem dsharpStep_i0 (j tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair 0 j) tbl) = packT (1 - j) 1 j := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd, Nat.sub_zero, selectFn_one]

end Proposition77

end DomainTheory.NeighbourhoodSystems
