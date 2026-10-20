/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise627.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}






variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

















section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










theorem toElementMap_strctMap (ψ : (funSpace V₀ V₁).Element) :
    strctMap.toElementMap ψ = strct ψ := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨M, hψM, _, hstrct⟩
    obtain ⟨hWmem, hg⟩ := hstrct
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
    refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    obtain ⟨hstepmem, hMsub⟩ := (hg p hp).1
    exact ⟨ψ.up_mem hψM hstepmem hMsub, (hg p hp).2⟩
  · rintro ⟨hWmem, hgψ⟩
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
    have hψL : ψ.mem (stepFun L) :=
      (mem_stepFun_iff ψ hL).mpr (fun p hp => (hgψ p hp).1)
    refine ⟨stepFun L, hψL, ψ.sub hψL, ⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    exact ⟨⟨ψ.sub (hgψ p hp).1, fun f hf => hf p hp⟩, (hgψ p hp).2⟩

end Part5
end Exercise627
end DomainTheory.Neighborhood
