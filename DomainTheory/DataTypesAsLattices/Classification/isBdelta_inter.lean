/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset
import DomainTheory.DataTypesAsLattices.Classification.Basic


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
