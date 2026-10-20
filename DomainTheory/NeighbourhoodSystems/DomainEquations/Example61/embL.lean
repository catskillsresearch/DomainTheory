/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- `1P = {(1::p, a) ∣ (p, a) ∈ P}`: the `1`-prefixed copy of a `D^§`-neighbourhood `P`. -/
def embL (P : Set (List Bool × α)) : Set (List Bool × α) := {t | ∃ p', t.1 = true :: p' ∧ (p', t.2) ∈ P}

end Example61
end DomainTheory.NeighbourhoodSystems
