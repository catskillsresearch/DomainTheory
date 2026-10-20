/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.not_mem_zero_cond_graph
public import DomainTheory.DataTypesAsLattices.Enumeration.cond_graph_eq_bot_iff

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices





/-- **Scott 1976, (3.1).** `cond(x)(y)(cond(x)(y)) = y`. -/
theorem eq_3_1 (x y : Pomega) :
    funOf (funOf (funOf condC x) y) (funOf (funOf condC x) y) = y := by
  rw [condC_beta3]
  by_cases hxy : x = botElem ∧ y = botElem
  · rcases hxy with ⟨rfl, rfl⟩
    have : funOf (funOf condC botElem) botElem = botElem :=
      (cond_graph_eq_bot_iff botElem botElem).mpr ⟨rfl, rfl⟩
    simp [condSet, botElem]
  · have hne : funOf (funOf condC x) y ≠ botElem := by
      intro h
      exact hxy ((cond_graph_eq_bot_iff x y).mp h)
    exact eq_2_7_pos x y (funOf (funOf condC x) y)
      (not_mem_zero_cond_graph x y) hne

end DomainTheory.DataTypesAsLattices
