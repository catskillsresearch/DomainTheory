/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Constructive
public import DomainTheory.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.Sum.SumToken
public import DomainTheory.InformationSystems.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.Sum.lftFinset
public import DomainTheory.InformationSystems.Sum.rhtFinset
public import DomainTheory.InformationSystems.Sum.SumCon

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Entailment for the separated sum (Scott 6.3(iv')–(iv''')).
Includes `SumCon` so `ent_con` can update projections. -/
def SumEnt (u : Finset (SumToken α β)) (p : SumToken α β) : Prop :=
  SumCon A B u ∧
    match p with
    | .bot => True
    | .left x => lftFinset u ≠ ∅ ∧ A.Ent (lftFinset u) x
    | .right y => rhtFinset u ≠ ∅ ∧ B.Ent (rhtFinset u) y

end InfoSys

end DomainTheory.InformationSystems
