/-ai
On two odd indices 2a+1 and 2b+1, the sharp decider step returns the pack of D's equality bit, D's consistency bit, and one more than twice D's intersection index, all at the pair of a and b.

Both outer selections see one minus an odd positive number, hence zero. Both parities are one, so both inner selections take the leaf branch, and dividing the odd indices by two recovers a and b.
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

theorem dsharpStep_ll (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 1) (2 * b + 1)) tbl)
      = packT (feq (Nat.pair a b)) (fcons (Nat.pair a b)) (2 * finter (Nat.pair a b) + 1) := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 1) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 1) = 0 by omega, selectFn_zero,
    show (2 * a + 1) % 2 = 1 by omega, selectFn_one,
    show (2 * b + 1) % 2 = 1 by omega, selectFn_one,
    show (2 * a + 1) / 2 = a by omega, show (2 * b + 1) / 2 = b by omega]

end Proposition77

end DomainTheory.NeighbourhoodSystems
