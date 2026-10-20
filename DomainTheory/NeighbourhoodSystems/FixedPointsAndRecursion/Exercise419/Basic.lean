module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.oneMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.oneDef
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.not_cone_subset_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_nil
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_false
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_true
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_bot_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.T
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation14
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation15
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.oneMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.oneMap_strBot

@[expose] public section

/-!
# Exercise 4.19 (Scott 1981, PRG-19, Lecture IV) — verifying Example 4.4

Example 4.4 leaves many assertions to the reader. This module discharges the two explicitly
requested ones:

* **"Peano's Axioms" for `{0,1}*`.** The structured set `⟨Σ*, Λ, 0·, 1·⟩` (here `Σ* = List Bool`,
  `Λ = []`, and the two successors `b ↦ b :: ·`) satisfies the natural two-successor analogue of
  Definition 4.5: `Λ` is not a successor (`peano_nil_ne_cons`), each successor is injective
  (`peano_cons_injective`), the two successor ranges are disjoint (`peano_cons_disjoint`), and the
  *induction* principle holds (`peano_induction`). So `Σ*` is the free monoid on two generators —
  the binary-tree analogue of `⟨ℕ, 0, ⁺⟩`.

* **`one : C → T` is definable from the rest of the structure by a fixed-point equation.** We first
  build the three tests `empty, zero, one : C → T` as honest approximable maps (Scott: "it is an
  exercise to show these are approximable"), via a uniform *head-test* combinator `liftC`. We then
  show

  `one(x) = cond(empty(x), false, cond(zero(x), false, true))`

  on every generator of `|C|` (`one_def_strElem`, `one_def_strBot`), exhibiting `one` as the
  solution of a fixed-point/recursion equation in the remaining structure `⟨C, Λ, 0, 1, empty,
  zero, cond⟩` (the right-hand side does not mention `one`, so this is the trivial fixed point —
  Scott's point that the tests are not independent).

The `liftC` combinator (a map `C → V` determined by its values on the partial elements `σ⊥` and the
total elements `σ`, subject to two monotonicity conditions) is reusable; with it one likewise gets
Scott's `tail : C → C` (`tail(bx) = x`, `tail(Λ) = ⊥`), here noted but not needed for `one`.

The `liftC` *data* is **choice-free**; the truth-domain tests inherit `Classical.choice`
structurally from `T` (Example 1.2), exactly as `Example23.parityMap` and `Example43.zeroMap` do.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

/-! ### "Peano's Axioms" for `{0,1}* = List Bool`. -/

/-! ### Disjointness facts for `C`'s neighbourhoods (cones vs singletons). -/



/-! ### The head-test value functions. -/

variable {β : Type*}




/-! ### The combinator `liftC`: an approximable map out of `C`. -/




/-! ### The three tests `empty, zero, one : C → T`. -/






/-! Value equations on total elements `σ` and partial elements `σ⊥`. -/


/-! ### `one` is defined from `empty`, `zero` and `cond` by a fixed-point equation. -/

end DomainTheory.NeighbourhoodSystems.Exercise419
