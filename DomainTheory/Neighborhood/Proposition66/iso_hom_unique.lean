/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition63
import DomainTheory.Neighborhood.Proposition66.Basic


namespace DomainTheory.Neighborhood

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}



/-- The isomorphism of Proposition 6.6 is **unique**: the homomorphism `A → B` realising it is the
only homomorphism between the two initial algebras. -/
theorem iso_hom_unique (hA : IsInitial A) (h : AlgHom A B) : h = hA.desc B :=
  hA.uniq B h

end DomainTheory.Neighborhood
