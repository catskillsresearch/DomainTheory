/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

variable (u : D.Element) (hu : u ≠ D.bot)

/-- The `D`-element corresponding to `t : O.Element` under `a`'s formula: `Z ↦ Z = Δ_D ∨ (t ∋ {0}
∧ u ∋ Z)`. This is a genuine `Element` (filter), built with no case-split on `t`. -/
def fixOfO (t : O.Element) : D.Element where
  mem Z := D.mem Z ∧ (Z = D.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ u.mem Z))
  sub h := h.1
  master_mem := ⟨D.master_mem, Or.inl rfl⟩
  inter_mem := by
    rintro Z Z' ⟨hZ, hZ1⟩ ⟨hZ', hZ1'⟩
    refine ⟨?_, ?_⟩
    · rcases hZ1 with rfl | ⟨-, huZ⟩
      · rwa [Set.inter_eq_right.mpr (D.sub_master hZ')]
      · rcases hZ1' with rfl | ⟨-, huZ'⟩
        · rwa [Set.inter_eq_left.mpr (D.sub_master hZ)]
        · exact u.sub (u.inter_mem huZ huZ')
    · rcases hZ1 with rfl | ⟨ht, huZ⟩
      · rcases hZ1' with rfl | ⟨ht', huZ'⟩
        · left; exact Set.inter_self _
        · right
          refine ⟨ht', ?_⟩
          rw [Set.inter_eq_right.mpr (D.sub_master hZ')]
          exact huZ'
      · right
        refine ⟨ht, ?_⟩
        rcases hZ1' with rfl | ⟨-, huZ'⟩
        · rw [Set.inter_eq_left.mpr (D.sub_master hZ)]
          exact huZ
        · exact u.inter_mem huZ huZ'
  up_mem := by
    rintro Z Z' ⟨hZ, hZ1⟩ hZ'D hZZ'
    refine ⟨hZ'D, ?_⟩
    rcases hZ1 with rfl | ⟨ht, huZ⟩
    · left; exact Set.Subset.antisymm (D.sub_master hZ'D) hZZ'
    · right; exact ⟨ht, u.up_mem huZ hZ'D hZZ'⟩

end DomainTheory.NeighbourhoodSystems
