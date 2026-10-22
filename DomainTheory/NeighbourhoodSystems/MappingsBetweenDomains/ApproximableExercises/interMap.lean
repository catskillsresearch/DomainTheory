module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.ApproximableMap₂

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 2.10 (Scott 1981, PRG-19).** The pointwise **intersection** `h` of two approximable
maps: `X h Z ↔ X f Z ∧ X g Z`. It is approximable, and (`mem_toElementMap_interMap`)
`h(x) = f(x) ∩ g(x)`. -/
def interMap (f g : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₁ where
  rel X Z := f.rel X Z ∧ g.rel X Z
  rel_dom h := f.rel_dom h.1
  rel_cod h := f.rel_cod h.1
  master_rel := ⟨f.master_rel, g.master_rel⟩
  inter_right := fun ⟨hf, hg⟩ ⟨hf', hg'⟩ => ⟨f.inter_right hf hf', g.inter_right hg hg'⟩
  mono := fun ⟨hf, hg⟩ hX'X hZZ' hX' hZ' =>
    ⟨f.mono hf hX'X hZZ' hX' hZ', g.mono hg hX'X hZZ' hX' hZ'⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
