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
"could be given for any category". The category is Mathlib's `CategoryTheory.Category`
(`Category.lean`); this module formalises the vocabulary on top of it:

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

The composition laws are the project's `idMap_comp` / `comp_idMap` / `comp_assoc` (Theorem 2.5).
`Endofunctor`, `TAlgebra`, `AlgHom`, and `IsInitial` stay the local structures: Mathlib's
`Limits.IsInitial` pulls `Classical.choice` into the statement of Lambek's lemma, and Scott's
Proposition 6.7 is the diagram chase in `Proposition67.lean`.
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
  comp f g := g.comp f
  id_comp f := ApproximableMap.comp_idMap f
  comp_id f := ApproximableMap.idMap_comp f
  assoc f g h := (ApproximableMap.comp_assoc h g f).symm

variable {Obj : Type u} [Category Obj]

/-! ### Definition 6.3 — functors -/


/-! ### Definition 6.4 — `T`-algebras and their homomorphisms -/


variable {T : Endofunctor Obj}


namespace AlgHom

/-- The identity is a homomorphism: `I ∘ k = k ∘ T(I)`. -/
def id (A : TAlgebra T) : AlgHom A A where
  hom := (𝟙 A.carrier)
  comm := by
    simp only [compAfter]
    rw [CategoryTheory.Category.comp_id, T.map_id, CategoryTheory.Category.id_comp]

/-- Composition of `T`-algebra homomorphisms (the `T`-algebras and homomorphisms form a category —
the remark after Definition 6.4). -/
def comp {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) : AlgHom A C where
  hom := β.hom ⊚ α.hom
  comm := by
    have hα := α.comm
    have hβ := β.comm
    have hmap := T.map_comp β.hom α.hom
    dsimp only [compAfter] at hα hβ hmap ⊢
    rw [← CategoryTheory.Category.assoc, hα, CategoryTheory.Category.assoc, hβ,
      ← CategoryTheory.Category.assoc, hmap]

@[simp] theorem id_hom (A : TAlgebra T) : (AlgHom.id A).hom = (𝟙 A.carrier) := rfl

@[simp] theorem comp_hom {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) :
    (β.comp α).hom = β.hom ⊚ α.hom := rfl

end AlgHom

/-! ### Definition 6.5 — initial `T`-algebras -/


end DomainTheory.NeighbourhoodSystems
