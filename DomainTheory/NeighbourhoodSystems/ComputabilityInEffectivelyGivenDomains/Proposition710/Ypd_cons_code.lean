/-ai
The enumeration of the successor of a pairing code is the down-set of the neighbourhood named by the first component, united with the enumeration of the second component.

Rewrite by the definition of the enumeration, the successor decoding equation and the unpairing equations, the cons law for unions of down-sets, and the definition again.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.UPX_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_def

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem Ypd_cons_code (v acc : ℕ) :
    V.Ypd P (Nat.pair v acc + 1) = V.upSet (P.X v) ∪ V.Ypd P acc := by
  rw [Ypd_def, decodeList_succ, unpair_pair_fst, unpair_pair_snd, V.UPX_cons P, ← V.Ypd_def P]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
