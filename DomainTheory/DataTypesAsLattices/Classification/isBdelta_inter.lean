/-ai
The intersection of two Bδ sets is a Bδ set.

Write the two sets as countable intersections of Boolean-open sets. The intersections of a set from the first family with a set from the second, indexed by unpairing a natural number into a pair, are Boolean open. An element lies in every such intersection precisely when it lies in every set of both families, by evaluating at the pairs (n, 0) and (0, m) and using that unpairing inverts pairing.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem isBdelta_inter {U V : Set Pomega} (hU : IsBdelta U) (hV : IsBdelta V) :
    IsBdelta (U ∩ V) := by
  obtain ⟨Bs, hB, rfl⟩ := hU
  obtain ⟨Cs, hC, rfl⟩ := hV
  refine ⟨fun n => Bs (unpair n).1 ∩ Cs (unpair n).2,
    fun n => (hB _).inter (hC _), ?_⟩
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n =>
      ⟨Set.mem_iInter.mp hx.1 (unpair n).1, Set.mem_iInter.mp hx.2 (unpair n).2⟩
  · intro hx
    constructor
    · refine Set.mem_iInter.mpr fun n => ?_
      simpa [unpair_pair] using (Set.mem_iInter.mp hx (pair n 0)).1
    · refine Set.mem_iInter.mpr fun m => ?_
      simpa [unpair_pair] using (Set.mem_iInter.mp hx (pair 0 m)).2

end DomainTheory.DataTypesAsLattices
