module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611Inst16
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ofMem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ofMem_subsystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- **The poset of subsystems is the family `subFam E`.** The subsystems of `E`, ordered by `◁`,
are order-isomorphic to `subFam E` ordered by `⊆`. A subsystem is sent to its family of
neighbourhoods `{X ∣ D.mem X}`, and recovered by `ofMem`; order is preserved and reflected by
Scott's remark `Subsystem.subsystem_iff_subset_of_common`. -/
def subIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o {𝒮 : Set (Set α) // 𝒮 ∈ subFam E} where
  toFun D := ⟨{X | D.1.mem X}, ⟨D.1, D.2, rfl⟩⟩
  invFun 𝒮 := ⟨ofMem E 𝒮.1 𝒮.2, ofMem_subsystem E 𝒮.1 𝒮.2⟩
  left_inv := by
    intro D
    apply Subtype.ext
    apply NeighborhoodSystem.ext
    · intro X; exact Iff.rfl
    · exact D.2.master_eq.symm
  right_inv := by
    intro 𝒮
    apply Subtype.ext
    ext X
    exact Iff.rfl
  map_rel_iff' := by
    intro a b
    show ({X | a.1.mem X} : Set (Set α)) ⊆ {X | b.1.mem X} ↔ a.1 ◁ b.1
    constructor
    · intro hsub
      refine (Subsystem.subsystem_iff_subset_of_common a.2 b.2).mpr ?_
      intro X hX
      exact hsub hX
    · intro hsub X hX
      exact hsub.sub hX

end DomainTheory.NeighbourhoodSystems.Proposition611
