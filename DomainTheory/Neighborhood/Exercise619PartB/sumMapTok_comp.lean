/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise619
import DomainTheory.Neighborhood.Definition613
import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise619PartB.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619





variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}







/-- **`(g₀ ∘ f₀) + (g₁ ∘ f₁) = (g₀ + g₁) ∘ (f₀ + f₁)`.** -/
theorem sumMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    (g₀ : ApproximableMap B₀.sys C₀.sys) (g₁ : ApproximableMap B₁.sys C₁.sys) :
    sumMapTok (g₀.comp f₀) (g₁.comp f₁) = (sumMapTok g₀ g₁).comp (sumMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩ | ⟨Y, Y'', ⟨Y', hf, hg⟩, rfl, rfl⟩)
    · exact ⟨sumTokMaster B₀.sys B₁.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.sum B₁).sys.master_mem, rfl⟩⟩
    · exact ⟨embBit false X', Or.inr (Or.inl ⟨X, X', hf, rfl, rfl⟩),
        Or.inr (Or.inl ⟨X', X'', hg, rfl, rfl⟩)⟩
    · exact ⟨embBit true Y', Or.inr (Or.inr ⟨Y, Y', hf, rfl, rfl⟩),
        Or.inr (Or.inr ⟨Y', Y'', hg, rfl, rfl⟩)⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, rfl, rfl⟩ | ⟨Y, Y', hf, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩ | ⟨Y, Y', -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, rfl⟩ | ⟨Y₂, Y'', hg, heq, -⟩
      · exact Or.inl ⟨Or.inr (Or.inl ⟨X, f₀.rel_dom hf, rfl⟩), rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inl ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩)
      · exact absurd heq (embBit_ne (by decide) (B₀.ne X' (f₀.rel_cod hf)))
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, -⟩ | ⟨Y₂, Y'', hg, heq, rfl⟩
      · exact Or.inl ⟨Or.inr (Or.inr ⟨Y, f₁.rel_dom hf, rfl⟩), rfl⟩
      · exact absurd heq (embBit_ne (by decide) (B₁.ne Y' (f₁.rel_cod hf)))
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inr ⟨Y, Y'', ⟨Y', hf, hg⟩, rfl, rfl⟩)

end Exercise619
end DomainTheory.Neighborhood
