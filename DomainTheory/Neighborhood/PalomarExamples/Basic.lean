/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88a
public import DomainTheory.Neighborhood.Example15
public import DomainTheory.Neighborhood.Exercise722Regular

@[expose] public section

/-!
# Palomar example embeddings

Concrete countable neighbourhood systems that instantiate `theorem_8_8`.
-/

namespace DomainTheory.Neighborhood.Example15

end DomainTheory.Neighborhood.Example15

namespace DomainTheory.Neighborhood.Exercise722

/-- Countability of the neighbourhoods of `S`, via the `SExpr` presentation.
Picking a preimage uses Mathlib's `Surjective.countable` (hence `Classical.choice`);
the syntax `SExpr` itself is countable choice-free. -/
instance Ssys_countable : Countable {S : Set (List Bool) // Ssys.mem S} := by
  classical
  let f (e : SExpr) : {S : Set (List Bool) // InS S} :=
    if h : (denote e).Nonempty then ⟨denote e, InS_denote_of_nonempty h⟩
    else ⟨Set.univ, InS.univ⟩
  have : Countable {S : Set (List Bool) // InS S} :=
    Function.Surjective.countable (f := f) fun ⟨X, hX⟩ => by
      obtain ⟨e, he⟩ := InS_exists_denote hX
      refine ⟨e, ?_⟩
      have hne : (denote e).Nonempty := he.symm ▸ hX.nonempty
      dsimp [f]
      rw [dite_eq_left hne]
      exact Subtype.ext he
  exact Countable.of_equiv ({S : Set (List Bool) // InS S})
    (Equiv.subtypeEquivRight fun _ => Ssys_mem.symm)
end DomainTheory.Neighborhood.Exercise722
