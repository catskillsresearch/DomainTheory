/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)



theorem LamCon_singleton_bot : LamCon A ({.bot} : Finset (RawLamToken α)) := by
  refine ⟨0, ?_⟩
  change lamAtomFinset _ ∈ A.Con ∧ lamFunFinset _ = ∅
  constructor
  · have h : lamAtomFinset ({.bot} : Finset (RawLamToken α)) = ∅ := by
      ext x
      constructor
      · intro hx; exact False.elim (nomatch mem_lamAtomFinset.1 hx)
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    rw [h]; exact A.con_empty
  · ext p
    constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)

end InfoSys
end DomainTheory.InformationSystems
