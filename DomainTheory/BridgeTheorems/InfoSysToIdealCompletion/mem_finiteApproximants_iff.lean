/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.Basic

@[expose] public section


namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)







theorem mem_finiteApproximants_iff {x : A.Element} {y : FiniteElement A} :
    y ∈ finiteApproximants A x ↔ (y : A.Element) ≤ x :=
  ⟨le_of_mem_finiteApproximants A, mem_finiteApproximants_of_le A⟩

end InfoSysToIdealCompletion
end DomainTheory.BridgeTheorems
