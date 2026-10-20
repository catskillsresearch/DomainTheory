/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
import all Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
import all Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import all Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.aRel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutS
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.fixOrderIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_inj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_le_of_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.aRel_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.aRel_combine
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.ext_U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_Ico0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_pos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_le1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_up
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.toElementMap_cutElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.le_iff_U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_le_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutS_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutS_bddBelow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutPoint_nonneg
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutPoint_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_cutPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_injective

@[expose] public section

/-!
# Exercise 8.11 (Scott 1981, PRG-19, Lecture VIII)

> Let `Q` be the set of rational numbers and define a neighbourhood system by the equation
> `R = {[0,r) ∣ r ∈ Q and 0 < r ≤ 1}`. Show that the following defines an approximable map
> `a : R → R`: `[0,r) a [0,s) iff r < s or r = s = 1`. Show in addition that `a` is a projection
> where the fixed-point set of `a` is in a one-one correspondence with the real numbers between
> `0` and `1` inclusive. (Hint: recall Dedekind cuts and show `≤` matches `⊑`.) Conclude that `a`
> is *not* finitary. (Hint: aside from `1`, there are no finite elements for `{x ∣ x = a(x)}`.)

## Contents

* `R` — the chain neighbourhood system `{[0,r) ∣ 0 < r ≤ 1}` over `ℚ` (`ofNestedOrDisjoint`, since
  the intervals are literally nested by `r`).
* `a` — Scott's map (`aRel`), shown approximable (`Exercise811.a`).
* `isRetraction_a` / `isProjection_a` — the two closure facts Scott asks for.
* `fixOrderIso` — the order isomorphism `Fix(a) ≃o Set.Icc (0:ℝ) 1` realizing Scott's Dedekind-cut
  correspondence (`c := 1 - t` is the "cut point", `t` the represented real, chosen so that `≤`
  literally matches `⊑`, i.e. `fixOrderIso` is monotone both ways by construction).
* `not_isFinitary_a` — `a` is *not* finitary: if it were, `Fix(a) ≃o Set.Icc (0:ℝ) 1` would transport
  to *some* domain `F`'s element poset, but every non-bottom element of `Set.Icc (0:ℝ) 1` fails
  Theorem 8.5's algebraic-compactness test (only `0`, matching Scott's lone finite element `⊥`, is
  compact) — contradicting that `F` (being a domain) has a non-bottom *principal* element as soon as
  it has more than one element.

Everything here inherits the ambient `Classical.choice` taint of Mathlib's `ℚ`/`ℝ` order
instances (as with `Definition87.lean`'s `𝒰`); no *further* choice is introduced beyond that and
one genuine classical case split (`by_contra`) used for the compactness contradiction.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-! ### The chain neighbourhood system `R = {[0,r) ∣ 0 < r ≤ 1}` -/







/-! ### Scott's map `a : R → R` -/






/-! ### `a` is a retraction and a projection -/

/-! ### The fixed-point set of `a`, via "up-sets" `U : ℚ → Prop` -/





/-! ### The correspondence with `Set.Icc (0 : ℝ) 1` -/





















/-! ### Non-finitarity -/
end DomainTheory.NeighbourhoodSystems.Exercise811
