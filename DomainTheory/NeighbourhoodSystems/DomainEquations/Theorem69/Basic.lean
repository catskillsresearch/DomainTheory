module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.homOpComp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.homOp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.isStrict_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.comp_mono_gen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.toStrictMap_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.toStrictFilter_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.homOpComp_mono

@[expose] public section

/-!
# Lecture VI — Theorem 6.9 (Scott 1981, PRG-19): homomorphisms out of a fixed point

> **THEOREM 6.9.** If the functor `T` is *continuous on maps* (Definition 6.8) and if `D ≅ T(D)`, so
> in particular `D` is a `T`-algebra, then for any `T`-algebra `k : T(E) → E` there is a homomorphism
> `h : D → E`.

Scott's proof. Let `i : T(D) → D` be the isomorphism making `D` a `T`-algebra and `j : D → T(D)` its
inverse. A homomorphism `h : D → E` must satisfy `h ∘ i = k ∘ T(h)`, equivalently the **fixed-point
equation**

`h = k ∘ T(h) ∘ j`.

The operator `λh. k ∘ T(h) ∘ j` on the **strict** function space `(D →⊥ E)` is approximable: the
inner `λh. T(h)` is approximable *precisely by Definition 6.8* (`ContinuousOnMaps`), and post- and
pre-composition with the fixed maps `k`, `j` is approximable too. Hence by the Lecture IV fixed-point
theory (Theorem 4.1, `fixElement`) it has a least fixed point `h`, the desired homomorphism.

## What the formalization does

We work over Scott's **strict** function space `(D →⊥ E) = strictFun D.sys E.sys` (Exercise 5.10),
exactly matching Definition 6.8.

* **`homOpComp`** — the strict composite `g ↦ k ∘ g ∘ j` as a `StrictMap`. Strictness of the composite
  uses that `j` is strict (any isomorphism of domains preserves `⊥`, `isStrict_of_comp_eq_id`) and `k`
  is strict (a morphism of Scott's *strict* category; carried as a hypothesis), so `T(h) ∘ j` and then
  `k ∘ (T(h) ∘ j)` stay strict.
* **`homOp`** — the post/pre-composition map `(T(D) →⊥ T(E)) → (D →⊥ E)`, `g ↦ k ∘ g ∘ j`, built by
  Exercise 2.8's `ofMono`. Its decisive **action lemma** `homOp_apply_filter` says
  `homOp(f̂) = (k ∘ f ∘ j)^` for every strict `f`; it is proved by reducing (through the strict
  representation `strictFunEquiv`) to single step neighbourhoods `[X, Z]`, where the "finite factoring"
  is just `N := [Y₁, Y₂]`.
* The operator is `Op = homOp ∘ Φ`, where `Φ` is Definition 6.8's witness that `λf. T(f)` is
  approximable. Its `fixElement` represents the strict map `h`; the fixed-point equation
  (`toElementMap_fixElement`) unwinds — via `Φ`'s defining property and `homOp_apply_filter` — to
  `h = k ∘ T(h) ∘ j`, which rearranges (using `j ∘ i = I`) to the homomorphism square
  `h ∘ i = k ∘ T(h)`.

The conclusion is `Nonempty {g : AlgHom ⟨D, i⟩ B // IsStrict g.hom}` — Scott's *existence* statement,
recording that the homomorphism is itself a strict map (it is `toStrictMap` of the fixed point), which
the uniqueness half of Theorem 6.14 consumes. Extracting `Φ` from the `Prop`-valued `ContinuousOnMaps`
is done by `Exists.elim` while proving a `Prop`, so it stays **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-! ### General helper lemmas (strictness and monotonicity of composition). -/





/-! ### The post/pre-composition operator on strict function spaces. -/

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)
  (k : ApproximableMap (T.obj E).sys E.sys)
  (hj : IsStrict j) (hk : IsStrict k)




end HomOp

/-! ### Theorem 6.9. -/
end DomainTheory.NeighbourhoodSystems
