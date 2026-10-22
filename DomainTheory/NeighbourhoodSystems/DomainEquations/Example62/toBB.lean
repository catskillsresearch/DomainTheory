module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.memB_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_inter_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.memB_embBit_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.BB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- **Example 6.2 — forward half of `B ≅ B + B`.** An element `x` of `B` is sent to the sum element
recording, for each branch, whether `x` reaches the `0`-copy `0X` (left summand) or the `1`-copy `1Y`
(right summand). -/
def toBB (x : B.Element) : BB.Element where
  mem W := W = sumMaster B B
    ∨ (∃ X, B.mem X ∧ W = inj₀ X ∧ x.mem (embBit false X))
    ∨ (∃ Y, B.mem Y ∧ W = inj₁ Y ∧ x.mem (embBit true Y))
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
      · have hz := x.inter_mem hzX hzX'; rw [embBit_inter] at hz; exact memB_embBit_inv (x.sub hz)
      · have hz := x.inter_mem hzX hzX'; rwa [embBit_inter] at hz
    · exfalso
      have hz := x.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := B_nonempty _ (x.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumMaster_inter_inj₁ hY], hzY⟩)
    · exfalso
      have hz := x.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := B_nonempty _ (x.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [inj₁_inter], ?_⟩)
      · have hz := x.inter_mem hzY hzY'; rw [embBit_inter] at hz; exact memB_embBit_inv (x.sub hz)
      · have hz := x.inter_mem hzY hzY'; rwa [embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact x.up_mem hzX (memB_embBit false hX') (embBit_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := B_nonempty X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := B_nonempty Y hY
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact x.up_mem hzY (memB_embBit true hY') (embBit_subset.mpr (inj₁_subset_inj₁.mp hsub))

end Example62

end DomainTheory.NeighbourhoodSystems
