/-ai
This file gathers and re-exports the identity endofunctor, the predicate of being continuous on maps, and the lemmas that the identity endofunctor fixes objects and morphisms.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.idEndofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.ContinuousOnMaps
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.idEndofunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.idEndofunctor_map

@[expose] public section

/-!
# Lecture VI — Definition 6.8 (Scott 1981, PRG-19): functors *continuous on maps*

> **DEFINITION 6.8.** On the category of domains and strict approximable maps a functor `T` is
> *continuous on maps* if for any systems `D` and `E` the induced mapping
> `λf. T(f) : (D →⊥ E) → (T(D) →⊥ T(E))` is approximable.

This is the continuity condition that powers Theorem 6.9 (existence of homomorphisms out of a fixed
point `D ≅ T(D)`): the homomorphism equation `h = k ∘ T(h) ∘ j` is a fixed-point equation for the map
`λh. k ∘ T(h) ∘ j`, and it has a solution precisely because `λh. T(h)` — hence the whole operator — is
itself an approximable (so continuous) self-map of a function-space domain.

## What the formalization uses

* **The category and the functor.** `T` is an `Endofunctor DomainObj` (Definition 6.3): an action
  `T.obj` on domains and `T.map` on the morphisms (here approximable maps, Theorem 2.5 laws).
* **The strict function space `(D →⊥ E)`.** This is *exactly* Scott's domain on the left of the
  induced map. The project already constructs it in `Exercise510.lean`: `strictFun D E` is the
  neighbourhood system whose elements are the **strict** approximable maps (`IsStrict f`, i.e.
  `f(⊥) = ⊥`), with the representation `strictFunEquiv : |D →⊥ E| ≃o StrictMap D E` mirroring
  Theorem 3.10. So this Definition is stated over Scott's strict maps verbatim, **not** the full
  function space.
* **"is approximable".** In this framework a function between domains is *approximable* exactly when
  it is the elementwise action (`toElementMap`) of an approximable map (Proposition 2.2 / Theorem
  3.10). So `λf. T(f)` being approximable is rendered as the existence of a witnessing
  `Φ : (D →⊥ E) → (T(D) →⊥ T(E))` (an `ApproximableMap` between the two strict function-space
  *domains*) whose action reproduces `T` on the underlying maps — transported across the
  representation `strictFunEquiv` via `toStrictFilter`/`toStrictMap`.

Because the witnessing equation reads off the underlying map of a `StrictMap`, it automatically forces
`T.map f` to be strict whenever `f` is (lemma `ContinuousOnMaps.isStrict_map`): a `T` continuous on
maps does restrict to Scott's subcategory of strict maps, as required.

## A design note on the category (strict maps vs. all maps)

Scott states 6.8 on the category of domains and *strict* maps, whereas the project's abstract spine
(Definitions 6.3–6.7) is built on the all-maps `DomainObj` category (its `Hom` is the full
`ApproximableMap`). We bridge the two faithfully without introducing a second, strict-map category
abstraction: the functor here is still `T : Endofunctor DomainObj` (acting on *all* maps), but the
continuity condition is stated over the *strict* function spaces `(D →⊥ E)`, and strictness-preservation
is then *derived* (`ContinuousOnMaps.isStrict_map`) rather than assumed. So `T` lives on the all-maps
category, yet "continuous on maps" pins down exactly the behaviour Scott asks for on the strict
subcategory — keeping Definition 6.8 coherent with the rest of the Lecture VI spine while remaining
literally about Scott's strict maps.

The identity functor is continuous on maps (`continuousOnMaps_id`), witnessing non-vacuity; its
representing `Φ` is the identity on the function space. Everything here is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems



end DomainTheory.NeighbourhoodSystems
