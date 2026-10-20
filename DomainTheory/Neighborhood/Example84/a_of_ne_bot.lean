/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.Product
public import DomainTheory.Neighborhood.Example84.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂











variable {α : Type*} {D : NeighborhoodSystem α}











variable (u : D.Element) (hu : u ≠ D.bot)



theorem a_of_ne_bot {x : D.Element} (hx : x ≠ D.bot) : (a u).toElementMap x = u := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a]
  constructor
  · rintro ⟨-, hZeq | ⟨-, huZ⟩⟩
    · exact hZeq ▸ u.master_mem
    · exact huZ
  · intro huZ
    exact ⟨u.sub huZ, Or.inr ⟨hx, huZ⟩⟩

end DomainTheory.Neighborhood
