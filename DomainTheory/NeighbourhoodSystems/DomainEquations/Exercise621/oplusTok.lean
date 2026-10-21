/-ai
The coalesced sum of two neighbourhood systems over strings consists of the sum master together with the false tags of proper neighbourhoods of the left system and the true tags of proper neighbourhoods of the right system, so the improper tagged copies of the two masters are omitted and the two bottoms are identified. The master is the sum master, which contains the empty string and belongs to the system. A false tag lies under the master because the underlying neighbourhood does, and likewise for a true tag. Every member is nonempty: the master contains the empty string, and a tag is nonempty by the corresponding component hypothesis. The intersection of two members, witnessed by a nonempty neighbourhood contained in both, stays in the system. Two masters, and a master meeting a tag, reduce by the intersection of the sum master with that tag. Two tags of the same bit reduce by the bit-embedding intersection; a master witness would place the empty string in a bit embedding, a same-bit witness is closed by the component intersection law with properness from the left-factor intersection lemma, and an opposite-bit witness contributes a string whose head bit cannot be both values. Opposite bits have empty intersection, contradicting nonemptiness of the witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.inter_ne_of_ne_left

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/-- **Exercise 6.21 — the coalesced sum system `𝒟₀ ⊕ 𝒟₁` over `{0,1}*`.** As `sumTok`, but the
improper copies `0Δ₀`, `1Δ₁` are removed (`X ≠ Δ₀`, `Y ≠ Δ₁`), so the two bottoms are identified. -/
def oplusTok (D₀ D₁ : NeighborhoodSystem Str)
    (h₀ : ∀ X, D₀.mem X → X.Nonempty) (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ X ≠ D₀.master ∧ W = embBit false X) ∨
    (∃ Y, D₁.mem Y ∧ Y ≠ D₁.master ∧ W = embBit true Y)
  master := sumTokMaster D₀ D₁
  master_nonempty := ⟨[], nil_mem_sumTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_sumTokMaster hX
    · exact embT_subset_sumTokMaster hY
  inter_mem := by
    have hne : ∀ W, (W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ X ≠ D₀.master ∧ W = embBit false X) ∨
        (∃ Y, D₁.mem Y ∧ Y ≠ D₁.master ∧ W = embBit true Y)) → (W : Set Str).Nonempty := by
      rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · exact ⟨[], nil_mem_sumTokMaster⟩
      · exact embBit_nonempty (h₀ X hX)
      · exact embBit_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩)
      · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embF hX]
        exact Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X ∩ X', D₀.inter_mem hX hX' hZ₀ (embBit_subset.mp hZsub),
            inter_ne_of_ne_left (D₀.sub_master hX) hXne, rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          obtain ⟨w', he, -⟩ := hZsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Z₁)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embT hY]
        exact Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)
      · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          obtain ⟨w', he, -⟩ := hZsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false Z₀)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
        · exact Or.inr (Or.inr ⟨Y ∩ Y', D₁.inter_mem hY hY' hZ₁ (embBit_subset.mp hZsub),
            inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
