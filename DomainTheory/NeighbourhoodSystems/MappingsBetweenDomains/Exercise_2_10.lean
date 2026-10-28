module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

namespace ApproximableMap

section
variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

def interMap (f g : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₁ where
  rel X Z := f.rel X Z ∧ g.rel X Z
  rel_dom h := f.rel_dom h.1
  rel_cod h := f.rel_cod h.1
  master_rel := ⟨f.master_rel, g.master_rel⟩
  inter_right := fun ⟨hf, hg⟩ ⟨hf', hg'⟩ => ⟨f.inter_right hf hf', g.inter_right hg hg'⟩
  mono := fun ⟨hf, hg⟩ hX'X hZZ' hX' hZ' =>
    ⟨f.mono hf hX'X hZZ' hX' hZ', g.mono hg hX'X hZZ' hX' hZ'⟩

theorem mem_toElementMap_interMap (f g : ApproximableMap V₀ V₁) (x : V₀.Element) {Z : Set β} :
    ((interMap f g).toElementMap x).mem Z ↔
      (f.toElementMap x).mem Z ∧ (g.toElementMap x).mem Z := by
  constructor
  · rintro ⟨X, hxX, hf, hg⟩
    exact ⟨⟨X, hxX, hf⟩, ⟨X, hxX, hg⟩⟩
  · rintro ⟨⟨X, hxX, hf⟩, ⟨X', hxX', hg⟩⟩
    have hxXX' : x.mem (X ∩ X') := x.inter_mem hxX hxX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hxXX'
    refine ⟨X ∩ X', hxXX', ?_, ?_⟩
    · exact f.mono hf Set.inter_subset_left subset_rfl hXX' (f.rel_cod hf)
    · exact g.mono hg Set.inter_subset_right subset_rfl hXX' (g.rel_cod hg)
end

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
