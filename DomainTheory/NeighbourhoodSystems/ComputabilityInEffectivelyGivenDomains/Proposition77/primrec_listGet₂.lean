/-ai
If the code and the index are primitive recursive functions of a parameter, then list lookup of those values is primitive recursive.

It is the paired lookup composed with the pair of the two functions, and unpairing that pair recovers the two arguments.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_listGet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `listGet` as a binary primrec composite. -/
theorem primrec_listGet₂ {c i : ℕ → ℕ} (hc : Nat.Primrec c) (hi : Nat.Primrec i) :
    Nat.Primrec (fun p => listGet (c p) (i p)) :=
  (primrec_listGet.comp (hc.pair hi)).of_eq fun p => by
    simp only [unpair_pair_fst, unpair_pair_snd]

end Proposition77

end DomainTheory.NeighbourhoodSystems
