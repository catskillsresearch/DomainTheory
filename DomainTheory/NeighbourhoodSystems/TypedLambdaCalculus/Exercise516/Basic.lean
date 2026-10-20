module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailSing
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.dMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shape
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.SLe
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_prefix
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_append
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_prefix
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.strBot_le_strBot_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.strBot_le_strElem_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.strElem_le_strElem_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.not_strElem_le_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tail_prefix
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tail_hcone
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tail_hsing
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.neg_hcone
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.neg_hsing
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.d_hcone
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.d_hsing
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.dMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.dMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.memC_shape
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem_true
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem_false
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shape_injective
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem_le_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_cons_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_cons_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.SLe_cons2
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.SLe_cons_inv
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_SLe
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeElem_mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shape_refine

@[expose] public section

/-!
# Exercise 5.16 (Scott 1981, PRG-19, Lecture V) — `neg`, `merge` and `d` on `C`

Returning to Example 4.4 (the domain `C` of finite or infinite binary sequences), this module gives
fixed-point/recursive definitions of three maps and verifies their characterizing equations:

* **`tail : C → C`** (`tail(bx) = x`, `tail(Λ) = ⊥`) — Scott's predecessor analogue, the item left to
  the reader in Example 4.4, built here with the head-test combinator `Exercise419.liftC`.
* **`neg : C → C`** with `neg(0x) = 1·neg(x)`, `neg(1x) = 0·neg(x)` — bit-complement. We solve the
  recursion in closed form via `liftC` (`neg(σ) = (flip σ)`, `flip = List.map not`), prove the
  recursion equations `neg_cons_false`/`neg_cons_true` (so it is *the* solution), and prove Scott's
  involution law **`neg(neg x) = x` for all `x ∈ |C|`** (`negMap_negMap`) — using that an approximable
  map is determined by its values on the finite elements `σ⊥`, `σ` (Exercise 2.8,
  `eq_of_toElementMap_principal`), so it suffices to check the two-fold complement on those, where it
  is `flip ∘ flip = id`.
* **`d : C → C`** (`d(Λ) = Λ`, `d(0x) = 00·d(x)`, `d(1x) = 11·d(x)`) — the bit-doubling map of
  Example 4.4, again via `liftC` (`d(σ) = double σ`).
* **`merge : C × C → C`** with `merge(εx, δy) = ε·δ·merge(x, y)` — bit-interleaving. Built directly as
  an approximable map out of `prod C C` from an explicit interleave value function `mergeVal`. The
  boundary that Scott flags (`merge(Λ, y)` etc.) is resolved by the unique *monotone* convention
  (`merge(Λ, y) = Λ`, `merge(εx, y) = ε⊥` once `y` runs out), the only choice compatible with
  approximability. We prove the recursion equation and **`merge(x, x) = d(x)`** (`mergeMap_diag`).

All *data* (`tail`, `negMap`, `dMap`, `mergeMap`) is **choice-free** (`#print axioms ⊆ {propext,
Quot.sound}`); equalities of maps go through `eq_of_toElementMap_principal` (classical, exactly like
the project's `ext_of_toElementMap`).

The Thue–Morse properties of `t = 0·merge(neg t, tail t)` (its digit-sum-mod-2 description and
overlap-freeness) are real combinatorics-on-words and are left as a separate follow-up.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-! ### List helpers: bit-complement `flip` and bit-doubling `double`. -/









/-! ### The approximation order on the finite elements `σ⊥` and `σ`. -/






/-! ### Determination by finite elements: an equality criterion for maps `C → V`. -/

variable {β : Type*}

/-! ### `tail : C → C` — Scott's predecessor analogue (Example 4.4). -/







/-! ### `neg : C → C` — bit complement, `neg(0x)=1·neg(x)`, `neg(1x)=0·neg(x)`. -/






/-! ### `d : C → C` — bit-doubling, `d(Λ)=Λ`, `d(0x)=00·d(x)`, `d(1x)=11·d(x)`. -/






/-! ### `merge : C × C → C` — bit interleaving.

The principal elements of `C` are tagged strings `(b, σ)`: `b = true` is the *total* `σ`, `b = false`
the *partial* `σ⊥`. We encode the corresponding neighbourhood (`shape`) and element (`shapeElem`),
the partial order between them (`SLe`), and the interleaving value function `mergeVal`. -/











/-! #### The monotonicity of `mergeVal` (the crux of approximability). -/





/-! #### A refinement lemma packaging both the representation and the order. -/


/-! #### The map `merge`. -/


@[simp] theorem consMap_shapeElem (b c : Bool) (σ : Str) :
    (consMap b).toElementMap (shapeElem c σ) = shapeElem c (b :: σ) := by
  cases c with
  | false => rw [shapeElem_false, consMap_strBot]; rfl
  | true => rw [shapeElem_true, consMap_strElem]; rfl

/-! #### Extensionality for maps `C × C → C` via finite element pairs. -/

/-! #### The recursion equation and `merge(x, x) = d(x)`. -/
end DomainTheory.NeighbourhoodSystems.Exercise516
