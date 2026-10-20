/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.subset_funion_left
public import DomainTheory.InformationSystems.InformationSystems.Constructive.subset_funion_right

@[expose] public section


namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]








/-- Universal property of the union: `u ∪' v ⊆ w` iff both `u ⊆ w` and `v ⊆ w`. -/
theorem funion_subset_iff {u v w : Finset α} : u ∪' v ⊆ w ↔ u ⊆ w ∧ v ⊆ w := by
  constructor
  · intro h
    exact ⟨fun x hx => h (subset_funion_left u v hx),
           fun x hx => h (subset_funion_right u v hx)⟩
  · rintro ⟨hu, hv⟩ x hx
    rcases mem_funion.1 hx with h | h
    exacts [hu h, hv h]

end DomainTheory.InformationSystems.Constructive
