/-ai
The image of the empty sequence under the isomorphism with the three-way sum is the left injection of the bottom element of the unit system.

The two elements contain the same neighbourhoods. In one direction the master is kept, the empty-sequence neighbourhood is the full token set of the unit bottom element, and neither bit-tagged neighbourhood belongs to the empty sequence. In the other direction the master is kept, and a neighbourhood of the unit bottom element is the full token set, which is the empty-sequence neighbourhood.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Example62C

open Example44 ExampleB Example62

/-- **`toCC Λ̂ = inj₀`.** The finished empty sequence is the terminator (the `𝟙`-summand). -/
theorem toCC_strElem_nil :
    toCC (strElem []) = sinj0 (V₁ := C) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
      (h₂ := C_nonempty) unitSys.bot := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨Set.univ, rfl, rfl, unitSys.bot.master_mem⟩
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
  · rintro (rfl | ⟨X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · obtain rfl : X = Set.univ := hX
      exact Or.inr (Or.inl ⟨rfl, memC_singleton [], subset_rfl⟩)

end Example62C

end DomainTheory.NeighbourhoodSystems
