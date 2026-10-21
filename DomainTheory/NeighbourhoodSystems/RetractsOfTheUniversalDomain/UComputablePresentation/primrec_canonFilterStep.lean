/-ai
The filter step is primitive recursive.

The clip code is primitive recursive, and selection on its nonempty test, between the successor of its pairing with zero and the constant zero, equals the filter step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClipCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.primrec_qpClipCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonFilterStep

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_canonFilterStep : Nat.Primrec canonFilterStep := by
  have hc : Nat.Primrec qpClipCode := primrec_qpClipCode
  exact (primrec_selectFn (primrec_qpNonemptyBop.comp hc)
    (Nat.Primrec.succ.comp (hc.pair (Nat.Primrec.const 0))) (Nat.Primrec.const 0)).of_eq
    fun _ => rfl

end DomainTheory.NeighbourhoodSystems
