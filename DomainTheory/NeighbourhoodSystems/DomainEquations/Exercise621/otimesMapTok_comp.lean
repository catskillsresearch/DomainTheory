module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}




variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}














variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}




/-- **`(g₀ ∘ f₀) ⊗ (g₁ ∘ f₁) = (g₀ ⊗ g₁) ∘ (f₀ ⊗ f₁)`** for **strict** `g₀, g₁`. -/
theorem otimesMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    {g₀ : ApproximableMap B₀.sys C₀.sys} {g₁ : ApproximableMap B₁.sys C₁.sys}
    (hg₀ : IsStrict g₀) (hg₁ : IsStrict g₁) :
    otimesMapTok (g₀.comp f₀) (g₁.comp f₁) = (otimesMapTok g₀ g₁).comp (otimesMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩,
      hXne, hYne, hX''ne, hY''ne, rfl, rfl⟩)
    · exact ⟨prodTokNbhd B₀.sys.master B₁.sys.master, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.otimes B₁).sys.master_mem, rfl⟩⟩
    · have hX'ne : X' ≠ B₀.sys.master := fun h => hX''ne (hg₀ (h ▸ hg0))
      have hY'ne : Y' ≠ B₁.sys.master := fun h => hY''ne (hg₁ (h ▸ hg1))
      exact ⟨prodTokNbhd X' Y',
        Or.inr ⟨X, Y, X', Y', hf0, hf1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩,
        Or.inr ⟨X', Y', X'', Y'', hg0, hg1, hX'ne, hY'ne, hX''ne, hY''ne, rfl, rfl⟩⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, Y, X', Y', hf0, hf1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨Xg, Yg, X'', Y'', -, -, hXgne, -, -, -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · have heq' : prodTokNbhd B₀.sys.master B₁.sys.master = prodTokNbhd Xg Yg := heq
        obtain ⟨h, -⟩ := prodTokNbhd_injective heq'
        exact absurd h.symm hXgne
    · rcases hW'W'' with ⟨-, rfl⟩ |
        ⟨Xg, Yg, X'', Y'', hg0, hg1, hXgne, hYgne, hX''ne, hY''ne, heq, rfl⟩
      · exact Or.inl ⟨otimesTok_mem_prod (f₀.rel_dom hf0) (f₁.rel_dom hf1) hXne hYne, rfl⟩
      · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
        exact Or.inr ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩,
          hXne, hYne, hX''ne, hY''ne, rfl, rfl⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
