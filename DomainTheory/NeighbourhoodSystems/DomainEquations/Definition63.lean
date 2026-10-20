/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.DomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.TAlgebra
public import DomainTheory.NeighbourhoodSystems.DomainEquations.AlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.IsInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Iso

@[expose] public section

/-!
# Lecture VI — Definitions 6.3–6.5 (Scott 1981, PRG-19): functors, `T`-algebras, initial algebras

To state domain equations `D ≅ T(D)` and single out their *canonical* solutions, Scott introduces
"a small amount of the terminology of category theory" and stresses that the next few definitions
"could be given for any category". This module sets up a small, self-contained category abstraction
and formalises that vocabulary:

* **Definition 6.3** — a *functor* `T` on a category into itself (an *endofunctor*), preserving
  identities and composition.
* **Definition 6.4** — a *`T`-algebra* `k : T(E) → E` and a *homomorphism* of `T`-algebras.
* **Definition 6.5** — an *initial* `T`-algebra: one with a unique homomorphism into every algebra.

Everything is generic over an arbitrary `Category`, exactly as Scott emphasises. As Scott also notes
in the prose preceding Definition 6.3 ("[the systems] form quite an interesting category with respect
to the approximable maps"), the neighbourhood systems and approximable maps of the project *are* a
category; that instance (`DomainObj`) is provided here as a witness that the abstract definitions are
not vacuous.

Auxiliary categorical lemmas (identity and composition of algebra homomorphisms, `Iso`) needed for
Propositions 6.6 and 6.7 are developed here as well.

All definitions and lemmas are constructive and **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); the underlying composition laws are the project's
`idMap_comp`/`comp_idMap`/`comp_assoc` (Theorem 2.5).

## Why a bespoke `Category` rather than Mathlib's `CategoryTheory.Category`?

Mathlib *does* have a fully developed category theory: `CategoryTheory.Category` (structurally
identical to the class below — separate object/morphism universes, `Hom`, `id`, `comp`, and the three
laws), functors `C ⥤ D`, `Iso`, `CategoryTheory.Endofunctor.Algebra`/`Algebra.Hom` with the category
of algebras, `Limits.IsInitial`, and even Lambek's lemma as `Endofunctor.Algebra.Initial.strInv` /
`left_inv` / `right_inv`. So Mathlib is *expressive enough* to state every one of Definitions 6.3–6.5
(and Propositions 6.6–6.7) verbatim — it is not a question of missing vocabulary.

It is nonetheless the wrong tool *here*, and the reason is this project's headline invariant, not
taste. The trade-off was checked empirically:

* The bare instance is fine: a `Category DomainObj` built on `ApproximableMap` (Theorem 2.5 laws)
  is **choice-free**, `#print axioms = [propext, Quot.sound]`.
* But the *only reason* to import Mathlib's hierarchy is to reuse its downstream content — functor
  algebras and the initial-algebra fixed-point theorem — and that content is **choice-bound**:
  `Mathlib.CategoryTheory.Endofunctor.Algebra.Initial.left_inv` (the inverse half of Lambek's lemma,
  i.e. Scott's Proposition 6.7) reports `[propext, Classical.choice, Quot.sound]`, because Mathlib's
  `IsInitial` rides on the `Limits` framework.
* By contrast, the project's own `initialIso` (Proposition 6.6) and `lambek` (Proposition 6.7), built
  on the class below, depend on **no axioms whatsoever** (`#print axioms` reports *"does not depend on
  any axioms"*).

So adopting Mathlib would force one of two losing choices: (a) consume its initial-algebra API and
thereby inject `Classical.choice` into the project's flagship Lecture VI results, breaking the
`#print axioms ⊆ {propext, Quot.sound}` discipline that is the whole point; or (b) take only the bare
class and re-prove 6.6–6.7 by hand anyway — paying a heavy transitive import and the `≫`
(diagrammatic, "`f` then `g`") vs `⊚` (Scott's "`g` after `f`") convention clash for no reusable
content. Since Scott asks only for "a small amount of the terminology of category theory", the
~50-line self-contained class below supplies exactly that vocabulary while keeping every proof
constructive and choice-free. The Mathlib `Category` is therefore *usable but counterproductive* for
this development, and is deliberately not used.
-/

namespace DomainTheory.NeighbourhoodSystems

universe u v w

/-! ### The category of neighbourhood systems and approximable maps

Scott's running category (prose before Definition 6.3). Objects bundle a token type with a system;
morphisms are approximable maps; the laws are Theorem 2.5. -/


/-- **The category of domains and approximable maps** (Scott's prose preceding Definition 6.3):
identities and associative composition come from Theorem 2.5 (`idMap_comp`, `comp_idMap`,
`comp_assoc`). -/
instance : Category DomainObj where
  Hom D E := ApproximableMap D.sys E.sys
  id D := ApproximableMap.idMap D.sys
  comp g f := g.comp f
  id_comp f := ApproximableMap.idMap_comp f
  comp_id f := ApproximableMap.comp_idMap f
  assoc h g f := ApproximableMap.comp_assoc h g f

variable {Obj : Type u} [Category Obj]

/-! ### Definition 6.3 — functors -/


/-! ### Definition 6.4 — `T`-algebras and their homomorphisms -/


variable {T : Endofunctor Obj}


namespace AlgHom

/-- The identity is a homomorphism: `I ∘ k = k ∘ T(I)`. -/
def id (A : TAlgebra T) : AlgHom A A where
  hom := Category.id A.carrier
  comm := by rw [Category.id_comp, T.map_id, Category.comp_id]

/-- Composition of `T`-algebra homomorphisms (the `T`-algebras and homomorphisms form a category —
the remark after Definition 6.4). -/
def comp {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) : AlgHom A C where
  hom := β.hom ⊚ α.hom
  comm := by
    rw [Category.assoc, α.comm, ← Category.assoc, β.comm, Category.assoc, ← T.map_comp]

@[simp] theorem id_hom (A : TAlgebra T) : (AlgHom.id A).hom = Category.id A.carrier := rfl

@[simp] theorem comp_hom {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) :
    (β.comp α).hom = β.hom ⊚ α.hom := rfl

end AlgHom

/-! ### Definition 6.5 — initial `T`-algebras -/


end DomainTheory.NeighbourhoodSystems
