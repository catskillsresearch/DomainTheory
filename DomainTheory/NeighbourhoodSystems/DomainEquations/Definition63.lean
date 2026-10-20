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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63Inst2

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



variable {Obj : Type u} [Category Obj]

/-! ### Definition 6.3 — functors -/


/-! ### Definition 6.4 — `T`-algebras and their homomorphisms -/


variable {T : Endofunctor Obj}


namespace AlgHom



@[simp] theorem id_hom (A : TAlgebra T) : (AlgHom.id A).hom = (𝟙 A.carrier) := rfl

@[simp] theorem comp_hom {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) :
    (β.comp α).hom = β.hom ⊚ α.hom := rfl

end AlgHom

/-! ### Definition 6.5 — initial `T`-algebras -/


end DomainTheory.NeighbourhoodSystems
