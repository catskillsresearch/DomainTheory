/-ai
Across the isomorphism of the sequence domain with the three-way sum of the unit and two copies of itself, prepending the bit false is the middle injection and prepending the bit true is the right injection.

The two elements contain the same neighbourhoods. If the bit is false, the master is kept, the empty-sequence neighbourhood is excluded, a neighbourhood tagged by the matching bit is membership for the cons map, and a neighbourhood tagged by the other bit is excluded; the converse restores the matching-bit membership. If the bit is true, the same case split with the two bit tags exchanged places the image in the right injection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consMap_mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consMap_not_mem_embBit_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consMap_not_mem_nil

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Example62C

open Example44 ExampleB Example62

/-- **`toCC ∘ (0·) = inj₁` and `toCC ∘ (1·) = inj₂`.** Prepending the bit `b` to `z` is, across the
isomorphism `C ≅ 𝟙+C+C`, the injection of `z` into the `b`-th `C`-summand. -/
theorem toCC_consMap (b : Bool) (z : C.Element) :
    toCC ((consMap b).toElementMap z)
      = cond b
          (sinj2 (V₀ := unitSys) (V₁ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z)
          (sinj1 (V₀ := unitSys) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  cases b
  · simp only [Bool.cond_false]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact Or.inr ⟨X, hX, rfl, (consMap_mem_embBit hX).mp hz⟩
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))
  · simp only [Bool.cond_true]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
      · exact Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mp hz⟩
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))

end Example62C

end DomainTheory.NeighbourhoodSystems
