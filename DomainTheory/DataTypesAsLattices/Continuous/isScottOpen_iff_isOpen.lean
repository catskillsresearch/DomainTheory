/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import DomainTheory.DataTypesAsLattices.Pomega
import DomainTheory.DataTypesAsLattices.Continuous.Basic
import DomainTheory.DataTypesAsLattices.Continuous.isOpen_basicNhhd
import DomainTheory.DataTypesAsLattices.Continuous.exists_basicNhhd_subset_of_generateOpen


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








/-- **Scott 1976, §1.** Scott-open sets are exactly the opens of the
positive information topology. -/
theorem isScottOpen_iff_isOpen (U : Set Pomega) : IsScottOpen U ↔ IsOpen U := by
  constructor
  · intro ⟨B, hU⟩
    rw [hU]
    exact isOpen_biUnion fun n _ => isOpen_basicNhhd n
  · intro hU
    refine ⟨{n | basicNhhd n ⊆ U}, ?_⟩
    ext x
    constructor
    · intro hx
      have hgen : GenerateOpen (Set.range memOpen) U := hU
      obtain ⟨n, hn, hsub⟩ := exists_basicNhhd_subset_of_generateOpen hgen hx
      exact Set.mem_iUnion₂.mpr ⟨n, hsub, hn⟩
    · intro hx
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      exact hn hxn

end DomainTheory.DataTypesAsLattices
