module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_eq_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjU_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- **Functoriality (composition): `Σ(g∘f) = Σg ∘ Σf`.** -/
theorem sumMapSig_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    sumMapSig (A := A) (h₀ := h₀) (h₁ := h₂) (g.comp f)
      = (sumMapSig (A := A) (h₀ := h₁) (h₁ := h₂) g).comp
          (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨hW, hW'', hd⟩
    rcases hd with rfl | ⟨hWU, rfl⟩ | ⟨a, X, Z'', rfl, rfl, Y', hf, hg⟩
    · exact ⟨masterSig V₁, ⟨hW, (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩,
        (sumSig A V₁ h₁).master_mem, hW'', Or.inl rfl⟩
    · exact ⟨jU, ⟨hW, Or.inr (Or.inl rfl), Or.inr (Or.inl ⟨hWU, rfl⟩)⟩,
        Or.inr (Or.inl rfl), hW'', Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨jc a Y', ⟨hW, Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩),
        Or.inr (Or.inr ⟨a, X, Y', rfl, rfl, hf⟩)⟩,
        Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩), hW'',
        Or.inr (Or.inr ⟨a, Y', Z'', rfl, rfl, hg⟩)⟩
  · rintro ⟨W', ⟨hW, hW', hdf⟩, -, hW'', hdg⟩
    refine ⟨hW, hW'', ?_⟩
    rcases hdg with rfl | ⟨hW'U, rfl⟩ | ⟨a, Y', Z'', hW'Y', rfl, hg⟩
    · exact Or.inl rfl
    · rcases hdf with rfl | ⟨hWU, -⟩ | ⟨a, X, Y'₀, -, hW'eq, hf⟩
      · exact absurd ((hW'U.symm) ▸ none_mem_masterSig) none_not_mem_jU
      · exact Or.inr (Or.inl ⟨hWU, rfl⟩)
      · obtain ⟨t, ht⟩ := h₁ Y'₀ (f.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'U) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
    · rcases hdf with rfl | ⟨-, hW'U⟩ | ⟨a', X, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Y'.symm) ▸ none_mem_masterSig) none_not_mem_jc
      · obtain ⟨t, ht⟩ := h₁ Y' (g.rel_dom hg)
        exact absurd ((hW'U.symm.trans hW'Y') ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
      · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₁ Y'₀ (f.rel_cod hf)) (hW'eq.symm.trans hW'Y')
        exact Or.inr (Or.inr ⟨a', X, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩)

end SumMapSig

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
