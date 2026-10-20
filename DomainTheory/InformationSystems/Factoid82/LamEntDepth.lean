/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.Factoid82.listToFinset
public import DomainTheory.InformationSystems.Factoid82.lamAtomInsert
public import DomainTheory.InformationSystems.Factoid82.lamFunInsert
public import DomainTheory.InformationSystems.Factoid82.lamAtomFinset
public import DomainTheory.InformationSystems.Factoid82.lamFunFinset
public import DomainTheory.InformationSystems.Factoid82.lamInUnionInsert
public import DomainTheory.InformationSystems.Factoid82.lamOutUnionInsert
public import DomainTheory.InformationSystems.Factoid82.lamInputUnion
public import DomainTheory.InformationSystems.Factoid82.lamOutputUnion
public import DomainTheory.InformationSystems.Factoid82.rawDepth
public import DomainTheory.InformationSystems.Factoid82.maxDepthInsert
public import DomainTheory.InformationSystems.Factoid82.finsetMaxDepth
public import DomainTheory.InformationSystems.Factoid82.LamConDepth
public import DomainTheory.InformationSystems.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.Factoid82.mem_listToFinset
public import DomainTheory.InformationSystems.Factoid82.mem_lamFunFinset
public import DomainTheory.InformationSystems.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.Factoid82.mem_lamInputUnion
public import DomainTheory.InformationSystems.Factoid82.mem_lamOutputUnion
public import DomainTheory.InformationSystems.Factoid82.max_le_max_nat
public import DomainTheory.InformationSystems.Factoid82.foldl_max_mono_init
public import DomainTheory.InformationSystems.Factoid82.foldl_max_ge_init
public import DomainTheory.InformationSystems.Factoid82.foldl_list_le_of_mem
public import DomainTheory.InformationSystems.Factoid82.rawDepth_funTok_gt_left
public import DomainTheory.InformationSystems.Factoid82.rawDepth_funTok_gt_right
public import DomainTheory.InformationSystems.Factoid82.LamEntDepthInst31
public import DomainTheory.InformationSystems.Factoid82.le_finsetMaxDepth_of_mem
public import DomainTheory.InformationSystems.Factoid82.foldr_max_le_of_forall
public import DomainTheory.InformationSystems.Factoid82.foldr_max_lt_of_forall
public import DomainTheory.InformationSystems.Factoid82.finsetMaxDepth_listToFinset_le
public import DomainTheory.InformationSystems.Factoid82.finsetMaxDepth_list_lt_funTok
public import DomainTheory.InformationSystems.Factoid82.finsetMaxDepth_list_lt_funTok_out
public import DomainTheory.InformationSystems.Factoid82.finsetMaxDepth_of_mem_funTok
public import DomainTheory.InformationSystems.Factoid82.finsetMaxDepth_inputUnion_lt
public import DomainTheory.InformationSystems.Factoid82.finsetMaxDepth_outputUnion_lt

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)
























/-! ## Depth measure (for well-founded Con) -/

























/-- Depth-based entailment as an inductive Prop (Scott (8)–(11)).
Premises are positive, so FunEnt-style recursion is allowed — unlike FunCon
inside an inductive `LamCon`. -/
inductive LamEntDepth : Finset (RawLamToken α) → RawLamToken α → Prop where
  | bot {u : Finset (RawLamToken α)}
      (hu : LamConDepth A u) : LamEntDepth u .bot
  | atom {u : Finset (RawLamToken α)} {x : α}
      (hu : LamConDepth A u)
      (hF : lamFunFinset u = ∅)
      (hne : lamAtomFinset u ≠ ∅)
      (hEnt : A.Ent (lamAtomFinset u) x) : LamEntDepth u (.atom x)
  | funTok {u : Finset (RawLamToken α)} {xs ys : List (RawLamToken α)}
      {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
      (hu : LamConDepth A u)
      (hA : lamAtomFinset u = ∅)
      (hConIn : LamConDepth A (listToFinset xs))
      (hConOut : LamConDepth A (listToFinset ys))
      (hs : s ⊆ lamFunFinset u)
      /- Function tokens are only entailed in the function world (cf. `SumEnt` right). -/
      (hWorld : lamFunFinset u ≠ ∅)
      /- Atom/bot inputs only when `xs` is atom-world — blocks mixed-world FunCon gaps. -/
      (hInCompat : lamFunFinset (listToFinset xs) = ∅ →
        lamFunFinset (lamInputUnion s) = ∅)
      (hEntIn : ∀ p ∈ s, ∀ z ∈ listToFinset p.1, LamEntDepth (listToFinset xs) z)
      (hEntOut : ∀ z ∈ listToFinset ys, LamEntDepth (lamOutputUnion s) z) :
      LamEntDepth u (.funTok xs ys)

end InfoSys
end DomainTheory.InformationSystems
