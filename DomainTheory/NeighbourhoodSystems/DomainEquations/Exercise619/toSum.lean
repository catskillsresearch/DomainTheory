/-ai
toSum is the forward half of the isomorphism from the concrete token sum to the abstract separated sum, a token-level analogue of the map toBB of Example 6.2. A neighbourhood of the image of a token element is the abstract sum master, or a left injection of a neighbourhood of the first system whose false-tagged copy belongs to the element, or a right injection of a neighbourhood of the second system whose true-tagged copy belongs to the element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_embF_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_embT_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_mem_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The forward half of the isomorphism, a token-level analogue of `Example62.toBB`. -/
def toSum (x : (sumTok D₀ D₁ h₀ h₁).Element) : (sum D₀ D₁ h₀ h₁).Element where
  mem W := W = sumMaster D₀ D₁
    ∨ (∃ X, D₀.mem X ∧ W = inj₀ X ∧ x.mem (embBit false X))
    ∨ (∃ Y, D₁.mem Y ∧ W = inj₁ Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ hY'], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := x.inter_mem hzX hzX'; rw [embBit_inter] at hz; exact sumTok_mem_embF_inv (x.sub hz)
      · have hz := x.inter_mem hzX hzX'; rwa [embBit_inter] at hz
    · exfalso
      have hz := x.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (x.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumMaster_inter_inj₁ hY], hzY⟩)
    · exfalso
      have hz := x.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (x.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [inj₁_inter], ?_⟩)
      · have hz := x.inter_mem hzY hzY'; rw [embBit_inter] at hz; exact sumTok_mem_embT_inv (x.sub hz)
      · have hz := x.inter_mem hzY hzY'; rwa [embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact x.up_mem hzX (sumTok_mem_embF hX') (embBit_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := h₀ X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := h₁ Y hY
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact x.up_mem hzY (sumTok_mem_embT hY') (embBit_subset.mpr (inj₁_subset_inj₁.mp hsub))

end Exercise619

end DomainTheory.NeighbourhoodSystems
