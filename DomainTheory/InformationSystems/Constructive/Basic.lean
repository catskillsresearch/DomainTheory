/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.Constructive.funion
public import DomainTheory.InformationSystems.Constructive.decidableEq_finset
public import DomainTheory.InformationSystems.Constructive.insert_comm'
public import DomainTheory.InformationSystems.Constructive.instLeftCommutativeInsert
public import DomainTheory.InformationSystems.Constructive.Basic.notation5
public import DomainTheory.InformationSystems.Constructive.mem_foldr_insert
public import DomainTheory.InformationSystems.Constructive.mem_funion
public import DomainTheory.InformationSystems.Constructive.funion_empty_right
public import DomainTheory.InformationSystems.Constructive.decidableEq_finset_eq_of_subset
public import DomainTheory.InformationSystems.Constructive.decidableEq_finset_false_of_ne

@[expose] public section

/-!
# A choice-free `Finset` prelude

One of the project's goals (Goal 3) is to certify that the *information-system*
presentation of Scott domains can be developed in a **purely constructive** fragment of
Lean: every result must have a `#print axioms` footprint contained in
`[propext, Quot.sound]`, with **no `Classical.choice`** and no use of the law of excluded
middle.

This is harder than it looks, because several of mathlib's `Finset` *operations* and even
a few basic *lemmas* transitively depend on `Classical.choice` (through the
`Multiset.dedup` / quotient machinery), in version `v4.30.0`:

* tainted operations: `(· ∪ ·)`, `Finset.image`, `(· ×ˢ ·)`, `Finset.biUnion`, `(· \ ·)`,
  and mathlib's `Finset.decidableEq` (via `Multiset` quotients);
* tainted lemmas: e.g. `Finset.insert_comm`, `Finset.singleton_subset_iff`;
* tainted *tactics*: `tauto`, `aesop` (they close goals via classical reasoning).

By contrast the following are choice-free and form our working toolkit: `insert`,
`(· ∩ ·)`, `Finset.filter`, `Finset.fold`, `Multiset.foldr`, the membership/subset lemmas
(`Finset.mem_insert`, `Finset.mem_singleton`, `Finset.subset_iff`, `Finset.mem_coe`,
`Finset.coe_subset`, `Finset.mem_inter`, `Finset.ext`), set-level unions/intersections,
and explicit term-mode/`rintro`/`constructor` proofs.

This file provides the finite-set operations the development needs but mathlib only
offers in choice-tainted form: a **binary union of `Finset`s**, built choice-free by
folding `insert`, and a **decidable equality** for `Finset` via subset antisymmetry.
Every declaration here is audited to depend only on
`[propext, Quot.sound]`.
-/

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]










end DomainTheory.InformationSystems.Constructive
