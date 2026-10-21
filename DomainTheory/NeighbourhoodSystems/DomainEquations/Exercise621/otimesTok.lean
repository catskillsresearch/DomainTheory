/-ai
The smash product of two neighbourhood systems over strings consists of the product neighbourhood of the two masters together with the product neighbourhoods of pairs of proper neighbourhoods. The full top rectangle is the master, and it contains the empty string. A proper rectangle lies under the master because inclusion of product neighbourhoods is componentwise and each coordinate lies under its master. The intersection of two members, witnessed by a neighbourhood contained in both, stays in the system. Two masters remain the master. A master meeting a proper rectangle reduces by the componentwise intersection of product neighbourhoods, because each coordinate lies under its master. Two proper rectangles rewrite the intersection as the rectangle of the intersected coordinates. If the witness is the master, componentwise inclusion puts a master inside one coordinate and antisymmetry with the opposite inclusion contradicts properness. If the witness is a proper rectangle, the component intersection laws close the two coordinates, and properness of each intersection is the left-factor intersection lemma.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.inter_ne_of_ne_left

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- **Exercise 6.21 — the smash product system `𝒟₀ ⊗ 𝒟₁` over `{0,1}*`.** As `prodTok`, but proper
rectangles must avoid both top coordinates (`X ≠ Δ₀`, `Y ≠ Δ₁`); the full top `M = prodTokNbhd Δ₀ Δ₁`
is kept as the master. -/
def otimesTok (D₀ D₁ : NeighborhoodSystem Str) : NeighborhoodSystem Str where
  mem W := W = prodTokNbhd D₀.master D₁.master ∨
    (∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ X ≠ D₀.master ∧ Y ≠ D₁.master ∧ W = prodTokNbhd X Y)
  master := prodTokNbhd D₀.master D₁.master
  master_nonempty := ⟨[], mem_prodTokNbhd_nil⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, Y, hX, hY, -, -, rfl⟩)
    · exact subset_rfl
    · exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, D₁.sub_master hY⟩
  inter_mem := by
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX'),
          Set.inter_eq_right.mpr (D₁.sub_master hY')]
        exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
      · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX),
          Set.inter_eq_right.mpr (D₁.sub_master hY)]
        exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · rw [prodTokNbhd_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, Z₁, hZ₀, hZ₁, -, -, rfl⟩
        · obtain ⟨hsub₀, -⟩ := prodTokNbhd_subset_iff.mp hZsub
          exact absurd (Set.Subset.antisymm (D₀.sub_master hX)
            (hsub₀.trans Set.inter_subset_left)) hXne
        · obtain ⟨hsub₀, hsub₁⟩ := prodTokNbhd_subset_iff.mp hZsub
          exact Or.inr ⟨X ∩ X', Y ∩ Y', D₀.inter_mem hX hX' hZ₀ hsub₀,
            D₁.inter_mem hY hY' hZ₁ hsub₁, inter_ne_of_ne_left (D₀.sub_master hX) hXne,
            inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
