/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section ClosureOperator

variable {a : ApproximableMap E E}

/-- **Compactness of a fixed point w.r.t. directed unions of `Fix(a)`.** Phrased via the ambient
`E.Element` order and `iSupDirected` (since `Fix(a)` is not itself a `NeighborhoodSystem.Element`
type), mirroring `Theorem85.lean`'s `IsCompactElt`. -/
def IsCompactFix (_h : IsClosureOperator a) (y : FixSet a) : Prop :=
  ∀ {I : Type u} [Nonempty I] (d : I → FixSet a)
    (hdir : ∀ i j, ∃ k, (d i).1 ≤ (d k).1 ∧ (d j).1 ≤ (d k).1),
    y.1 ≤ iSupDirected (fun i => (d i).1) hdir → ∃ i, y.1 ≤ (d i).1

end ClosureOperator

end DomainTheory.NeighbourhoodSystems
