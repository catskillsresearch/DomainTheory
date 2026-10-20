/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise619PartB
public import DomainTheory.Neighborhood.Exercise621.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}




variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}














variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`(g₀ ∘ f₀) ⊕ (g₁ ∘ f₁) = (g₀ ⊕ g₁) ∘ (f₀ ⊕ f₁)`** for **strict** `g₀, g₁`. (Strictness of the
outer maps is exactly what prevents an intermediate top `f₀(X) = Δ₀'` from being re-expanded — that
is the categorical reason `⊕` is a functor only on the strict-map category Scott restricts to.) -/
theorem oplusMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    {g₀ : ApproximableMap B₀.sys C₀.sys} {g₁ : ApproximableMap B₁.sys C₁.sys}
    (hg₀ : IsStrict g₀) (hg₁ : IsStrict g₁) :
    oplusMapTok (g₀.comp f₀) (g₁.comp f₁) = (oplusMapTok g₀ g₁).comp (oplusMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, hXne, hX''ne, rfl, rfl⟩ |
      ⟨Y, Y'', ⟨Y', hf, hg⟩, hYne, hY''ne, rfl, rfl⟩)
    · exact ⟨sumTokMaster B₀.sys B₁.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.oplus B₁).sys.master_mem, rfl⟩⟩
    · have hX'ne : X' ≠ B₀.sys.master := fun h => hX''ne (hg₀ (h ▸ hg))
      exact ⟨embBit false X', Or.inr (Or.inl ⟨X, X', hf, hXne, hX'ne, rfl, rfl⟩),
        Or.inr (Or.inl ⟨X', X'', hg, hX'ne, hX''ne, rfl, rfl⟩)⟩
    · have hY'ne : Y' ≠ B₁.sys.master := fun h => hY''ne (hg₁ (h ▸ hg))
      exact ⟨embBit true Y', Or.inr (Or.inr ⟨Y, Y', hf, hYne, hY'ne, rfl, rfl⟩),
        Or.inr (Or.inr ⟨Y', Y'', hg, hY'ne, hY''ne, rfl, rfl⟩)⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hf, hYne, hY'ne, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, -, -, heq, -⟩ | ⟨Y, Y', -, -, -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, -, hX''ne, heq, rfl⟩ | ⟨Y₂, Y'', hg, -, -, heq, -⟩
      · exact Or.inl ⟨oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) (f₀.rel_dom hf) hXne, rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inl ⟨X, X'', ⟨X', hf, hg⟩, hXne, hX''ne, rfl, rfl⟩)
      · exact absurd heq (embBit_ne (by decide) (B₀.ne X' (f₀.rel_cod hf)))
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, -, -, heq, -⟩ | ⟨Y₂, Y'', hg, -, hY''ne, heq, rfl⟩
      · exact Or.inl ⟨oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) (f₁.rel_dom hf) hYne, rfl⟩
      · exact absurd heq (embBit_ne (by decide) (B₁.ne Y' (f₁.rel_cod hf)))
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inr ⟨Y, Y'', ⟨Y', hf, hg⟩, hYne, hY''ne, rfl, rfl⟩)

end Exercise619
end DomainTheory.Neighborhood
