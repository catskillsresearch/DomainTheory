/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.Neighborhood.Exercise813c.Basic

@[expose] public section


namespace DomainTheory.Neighborhood








theorem generatedBy_genPoint_box (I : Finset ℕ) (f : ℕ → Bool) :
    GeneratedBy genPoint (box I f) := by
  induction I using Finset.induction_on with
  | empty => simpa [box] using GeneratedBy.univ
  | insert a s ha ih =>
    have hstep : box (insert a s) f =
        (if f a = true then genPoint a else (genPoint a)ᶜ) ∩ box s f := by
      ext x
      by_cases hfa : f a = true
      · simp [hfa]
      · have hfa' : f a = false := by simpa using hfa
        simp [hfa]
    rw [hstep]
    split_ifs with hfa
    · exact (GeneratedBy.of a).inter ih
    · exact (GeneratedBy.of a).compl.inter ih

end DomainTheory.Neighborhood
