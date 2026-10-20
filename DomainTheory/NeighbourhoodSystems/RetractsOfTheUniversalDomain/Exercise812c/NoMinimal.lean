/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Atomlessness** ("no minimal neighbourhoods"), generalizing `U_no_minimal`/`V_no_minimal`:
every non-empty neighbourhood splits into two disjoint, non-empty neighbourhood pieces whose union
recovers it. (Phrased with explicit `Nonempty` clauses, equivalent given `Y ∩ Z = ∅`/`Y ∪ Z = X` to
`U_no_minimal`/`V_no_minimal`'s own `Y ≠ X`/`Z ≠ X` phrasing, but directly what `exists_split'`
needs — an *abstract* `D.mem` need not itself carry nonemptiness the way `U.mem`/`V.mem` do.) -/
def NeighborhoodSystem.NoMinimal {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X : Set α}, D.mem X →
    ∃ Y Z : Set α, D.mem Y ∧ D.mem Z ∧ Y.Nonempty ∧ Z.Nonempty ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X

end DomainTheory.NeighbourhoodSystems
