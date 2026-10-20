/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.InfoSys

@[expose] public section

universe u

namespace DomainTheory.InformationSystems
namespace InfoSys

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

/-- An *element* (ideal) of the domain: a set of tokens that is consistent on every
finite subset and closed under entailment. -/
structure Element where
  /-- The underlying set of tokens. -/
  carrier : Set α
  /-- Every finite subset of the element is consistent. -/
  consistent : ∀ Y : Finset α, (Y : Set α) ⊆ carrier → Y ∈ sys.Con
  /-- The element is closed under entailment. -/
  closed : ∀ (Y : Finset α) (a : α), (Y : Set α) ⊆ carrier → sys.Ent Y a → a ∈ carrier

end InfoSys
end DomainTheory.InformationSystems
