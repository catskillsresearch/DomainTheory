/-ai
The coalesced-sum action of two approximable maps relates W to W' in one of three ways: W is a neighbourhood of the coalesced sum and W' is the sum master of the codomains; or proper neighbourhoods X and X' are related by the left map and W, W' are their false tags; or proper neighbourhoods Y and Y' are related by the right map and W, W' are their true tags. The domain and codomain of a related pair are the corresponding membership clauses of the coalesced sum. The master relates to the master. Intersection on the right proceeds by cases on the two relations: two master outputs intersect as the master, a master output meeting a proper tag reduces by the intersection of the sum master with that tag, two tags of the same bit use injectivity of the bit embedding and the component intersection law, with properness of the intersected codomain given by the left-factor intersection lemma, and opposite bits are distinct. Monotonicity likewise cases on the relation. A master output is forced because the master lies under every neighbourhood. A proper left output whose larger codomain is the master returns the master clause; whose larger codomain is a left tag either places the empty string in a bit embedding, applies the component monotonicity law after unpacking the two bit-embedding inclusions, or is an inclusion of opposite bits; and whose larger codomain is a right tag is an inclusion of opposite bits. A proper right output is symmetric.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.inter_ne_of_ne_left
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplus
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok_mem_embT

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

/-- **`f₀ ⊕ f₁`, the action of the coalesced sum on maps.** -/
def oplusMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.oplus A₁).sys (B₀.oplus B₁).sys where
  rel W W' :=
    ((A₀.oplus A₁).sys.mem W ∧ W' = sumTokMaster B₀.sys B₁.sys) ∨
    (∃ X X', f₀.rel X X' ∧ X ≠ A₀.sys.master ∧ X' ≠ B₀.sys.master ∧
      W = embBit false X ∧ W' = embBit false X') ∨
    (∃ Y Y', f₁.rel Y Y' ∧ Y ≠ A₁.sys.master ∧ Y' ≠ B₁.sys.master ∧
      W = embBit true Y ∧ W' = embBit true Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, hXne, -, rfl, -⟩ | ⟨Y, Y', hrel, hYne, -, rfl, -⟩)
    · exact hW
    · exact oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) (f₀.rel_dom hrel) hXne
    · exact oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) (f₁.rel_dom hrel) hYne
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, hX'ne, -, rfl⟩ | ⟨Y, Y', hrel, -, hY'ne, -, rfl⟩)
    · exact Or.inl rfl
    · exact oplusTok_mem_embF (h₀ := B₀.ne) (h₁ := B₁.ne) (f₀.rel_cod hrel) hX'ne
    · exact oplusTok_mem_embT (h₀ := B₀.ne) (h₁ := B₁.ne) (f₁.rel_cod hrel) hY'ne
  master_rel := Or.inl ⟨(A₀.oplus A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, hWeq, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr (Or.inl ⟨X, X', hrel, hXne, hX'ne, hWeq,
          by rw [sumTokMaster_inter_embF (f₀.rel_cod hrel)]⟩)
      · exact Or.inr (Or.inr ⟨Y, Y', hrel, hYne, hY'ne, hWeq,
          by rw [sumTokMaster_inter_embT (f₁.rel_cod hrel)]⟩)
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hX₂ne, hX'₂ne, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, -, -, hWeq, rfl⟩
      · refine Or.inr (Or.inl ⟨X, X', hrel, hXne, hX'ne, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embF (f₀.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inl ⟨X, X' ∩ X'₂, f₀.inter_right hrel hrel₂, hXne,
          inter_ne_of_ne_left (B₀.sys.sub_master (f₀.rel_cod hrel)) hX'ne, rfl,
          embBit_inter false X' X'₂⟩)
      · exact absurd hWeq (embBit_ne (by decide) (A₀.ne X (f₀.rel_dom hrel)))
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, -, -, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hY₂ne, hY'₂ne, hWeq, rfl⟩
      · refine Or.inr (Or.inr ⟨Y, Y', hrel, hYne, hY'ne, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embT (f₁.rel_cod hrel)]
      · exact absurd hWeq (embBit_ne (by decide) (A₁.ne Y (f₁.rel_dom hrel)))
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inr ⟨Y, Y' ∩ Y'₂, f₁.inter_right hrel hrel₂, hYne,
          inter_ne_of_ne_left (B₁.sys.sub_master (f₁.rel_cod hrel)) hY'ne, rfl,
          embBit_inter true Y' Y'₂⟩)
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hW'' hZ'
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩
    · exact Or.inl ⟨hW'', Set.Subset.antisymm ((B₀.oplus B₁).sys.sub_master hZ') hZZ'⟩
    · rcases hZ' with rfl | ⟨X₃, hX₃, hX₃ne, rfl⟩ | ⟨Y₃, hY₃, hY₃ne, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · rcases hW'' with rfl | ⟨X₂, hX₂, hX₂ne, rfl⟩ | ⟨Y₂, hY₂, hY₂ne, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X₂, X₃,
            f₀.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃,
            hX₂ne, hX₃ne, rfl, rfl⟩)
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₁.ne Y₂ hY₂) hsub)
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₀.ne X' (f₀.rel_cod hrel)) hsub)
    · rcases hZ' with rfl | ⟨X₃, hX₃, hX₃ne, rfl⟩ | ⟨Y₃, hY₃, hY₃ne, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₁.ne Y' (f₁.rel_cod hrel)) hsub)
      · rcases hW'' with rfl | ⟨X₂, hX₂, hX₂ne, rfl⟩ | ⟨Y₂, hY₂, hY₂ne, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₀.ne X₂ hX₂) hsub)
        · exact Or.inr (Or.inr ⟨Y₂, Y₃,
            f₁.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hY₂ hY₃,
            hY₂ne, hY₃ne, rfl, rfl⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
