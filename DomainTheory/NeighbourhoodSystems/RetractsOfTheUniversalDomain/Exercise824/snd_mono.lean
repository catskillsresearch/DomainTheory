/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise823
public import DomainTheory.Neighborhood.Exercise824.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}









theorem snd_mono {z z' : (PairSpace (E := E)).Element} (h : z ≤ z') : z.snd ≤ z'.snd := by
  intro X hX
  rw [mem_snd] at hX ⊢
  exact ⟨hX.1, h _ hX.2⟩

end Exercise824
end DomainTheory.Neighborhood
