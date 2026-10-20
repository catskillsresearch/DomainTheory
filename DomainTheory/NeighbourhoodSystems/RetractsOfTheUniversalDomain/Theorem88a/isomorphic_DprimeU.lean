/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88.Basic
public import DomainTheory.Neighborhood.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.Neighborhood.Definition610
public import DomainTheory.Neighborhood.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import DomainTheory.Neighborhood.Theorem88a.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*}







section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)




/-- **First sentence of Theorem 8.8 (isomorphism half).** `D ≅ᴰ D'`. -/
theorem isomorphic_DprimeU : D ≅ᴰ DprimeU D e hcover he0 := ⟨domainIso D e hcover he0⟩

end Iso
end DomainTheory.Neighborhood
