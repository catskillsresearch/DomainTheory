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
import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
import DomainTheory.DataTypesAsLattices.Continuous.isScottContinuous_monotone
import DomainTheory.DataTypesAsLattices.Continuous.isOpen_memOpen
import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_iff_isOpen


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








/-- Scott continuity coincides with topological continuity `Pω → Pω`. -/
theorem isScottContinuous_iff_continuous (f : Pomega → Pomega) :
    IsScottContinuous f ↔ Continuous f := by
  constructor
  · intro hf
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨k, rfl⟩
    rw [← isScottOpen_iff_isOpen]
    refine ⟨{n | k ∈ f (e n)}, ?_⟩
    ext x
    constructor
    · intro hx
      have : k ∈ scottUnion f x := by rwa [← hf x]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, hkn, hn⟩
    · intro hx
      obtain ⟨n, hkn, hn⟩ := Set.mem_iUnion₂.mp hx
      exact isScottContinuous_monotone hf hn hkn
  · intro hfcont x
    ext k
    have hopen : IsScottOpen (f ⁻¹' memOpen k) :=
      (isScottOpen_iff_isOpen _).mpr (IsOpen.preimage hfcont (isOpen_memOpen k))
    constructor
    · intro hk
      obtain ⟨B, hB⟩ := hopen
      have hx : x ∈ ⋃ n ∈ B, basicNhhd n := by
        have : x ∈ f ⁻¹' memOpen k := hk
        rwa [hB] at this
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      have hen : k ∈ f (e n) := by
        have : e n ∈ f ⁻¹' memOpen k := by
          rw [hB]
          exact Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩
        exact this
      exact mem_scottUnion.mpr ⟨n, hxn, hen⟩
    · intro hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
      have : e n ∈ f ⁻¹' memOpen k := hkn
      exact isScottOpen_isUpper hopen this hn

end DomainTheory.DataTypesAsLattices
