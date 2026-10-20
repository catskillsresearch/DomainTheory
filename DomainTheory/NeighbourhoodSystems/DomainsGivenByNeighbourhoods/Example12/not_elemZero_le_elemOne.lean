/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example12























namespace neighborhoodSystem

open NeighborhoodSystem







/-- **`elemZero` and `elemOne` are incomparable.** Neither total element approximates the other:
if it did, its finite neighbourhood `{i}` would have to belong to the other's filter too, which
is neither `Δ` nor its own singleton `{1-i}`. Used to show `⊥` is the *only* common lower bound
of `elemZero` and `elemOne` (Exercise 2.16's uniqueness argument for the parity map). -/
theorem not_elemZero_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h zero (Or.inr rfl) with h' | h'
  · exact zero_ne_master h'
  · exact zero_ne_one h'

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
