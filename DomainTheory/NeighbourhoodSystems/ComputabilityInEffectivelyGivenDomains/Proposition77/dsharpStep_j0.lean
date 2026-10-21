/-ai
If the first index is nonzero and the second index is zero, the sharp decider step returns the pack of one minus the first index, one, and the first index.

Unfolding the step, one minus the nonzero index is zero, so the outer selection takes the inner branch, and one minus zero then selects that pack.
ai-/
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

theorem dsharpStep_j0 {i : ℕ} (tbl : ℕ) (hi : i ≠ 0) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair i 0) tbl) = packT (1 - i) 1 i := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - i = 0 by omega, selectFn_zero, Nat.sub_zero, selectFn_one]

end Proposition77

end DomainTheory.NeighbourhoodSystems
