/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.FinSupp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]

variable (D) in
/-- **Exercise 6.29 — the indexed product `∏_i D_i`.** The index type is non-empty so the
dependent-sum token set contains a token. Neighbourhoods are cylinders: tuples `X i ∈ 𝒟ᵢ`
that are the master in all but finitely many coordinates. -/
def iprod : NeighborhoodSystem (Σ i, α i) where
  mem W := ∃ X : ∀ i, Set (α i), (∀ i, (D i).mem (X i)) ∧ FinSupp D X ∧ W = iprodNbhd X
  master := iprodNbhd (fun i => (D i).master)
  master_nonempty := by
    cases ‹Nonempty ι› with
    | intro i =>
      obtain ⟨a, ha⟩ := (D i).master_nonempty
      exact ⟨⟨i, a⟩, ha⟩
  master_mem := ⟨fun i => (D i).master, fun i => (D i).master_mem, FinSupp.master, rfl⟩
  sub_master := by
    rintro W ⟨X, hX, _, rfl⟩
    exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i)
  inter_mem := by
    rintro W W' Z ⟨X, hX, hXf, rfl⟩ ⟨X', hX', hX'f, rfl⟩ ⟨ZZ, hZZ, _, rfl⟩ hsub
    rw [iprodNbhd_inter] at hsub ⊢
    refine ⟨fun i => X i ∩ X' i, fun i => ?_, hXf.inter hX'f, rfl⟩
    have : ZZ i ⊆ X i ∩ X' i := iprodNbhd_subset_iff.mp hsub i
    exact (D i).inter_mem (hX i) (hX' i) (hZZ i) this

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
