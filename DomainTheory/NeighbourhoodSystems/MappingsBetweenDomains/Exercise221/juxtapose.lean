module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.subset_singleton_eq
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_prepend
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_subset_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Juxtaposition `xy`** as an approximable map `𝒞 × 𝒞 → 𝒞`.

The relation `X, Y j Z` reads off the *left-to-right bias*: if the first input neighbourhood `X` is
a cone `σΣ*` (`x` extends `σ` but is undetermined), the output only commits to the prefix `σ`
(`σΣ* ⊆ Z`), ignoring `Y`; if `X` is a terminator `{σ}` (`x` is the total finite sequence `σ`), the
output prepends `σ` to the second input `Y` (`σY ⊆ Z`). -/
def juxtapose : ApproximableMap₂ C C C where
  rel X Y Z := C.mem Y ∧ C.mem Z ∧
    ((∃ σ, X = cone σ ∧ cone σ ⊆ Z) ∨ (∃ σ, X = ({σ} : Set Str) ∧ prepend σ Y ⊆ Z))
  rel_dom₀ := by
    rintro X Y Z ⟨_, _, (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)⟩
    · exact memC_cone σ
    · exact memC_singleton σ
  rel_dom₁ := fun ⟨hY, _, _⟩ => hY
  rel_cod := fun ⟨_, hZ, _⟩ => hZ
  master_rel := ⟨C.master_mem, C.master_mem,
    Or.inl ⟨[], C_master.trans cone_nil.symm, by rw [C_master]; exact Set.subset_univ _⟩⟩
  inter_right := by
    rintro X Y Z Z' ⟨hY, hZ, hd⟩ ⟨_, hZ', hd'⟩
    rcases hd with ⟨σ, rfl, hsub⟩ | ⟨σ, rfl, hsub⟩
    · rcases hd' with ⟨σ', hX', hsub'⟩ | ⟨σ', hX', _⟩
      · obtain rfl : σ = σ' := cone_injective hX'
        exact ⟨hY, C.inter_mem hZ hZ' (memC_cone σ) (Set.subset_inter hsub hsub'),
          Or.inl ⟨σ, rfl, Set.subset_inter hsub hsub'⟩⟩
      · exact absurd hX' (cone_ne_singleton σ σ')
    · rcases hd' with ⟨σ', hX', _⟩ | ⟨σ', hX', hsub'⟩
      · exact absurd hX'.symm (cone_ne_singleton σ' σ)
      · obtain rfl : σ = σ' := by
          have := hX'; rw [Set.singleton_eq_singleton_iff] at this; exact this
        exact ⟨hY, C.inter_mem hZ hZ' (memC_prepend σ hY) (Set.subset_inter hsub hsub'),
          Or.inr ⟨σ, rfl, Set.subset_inter hsub hsub'⟩⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨hY, _, hd⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    refine ⟨hY', hZ', ?_⟩
    rcases hd with ⟨σ, rfl, hsub⟩ | ⟨σ, rfl, hsub⟩
    · rcases hX' with ⟨σ', rfl⟩ | ⟨σ', rfl⟩
      · exact Or.inl ⟨σ', rfl, (hX'X.trans hsub).trans hZZ'⟩
      · refine Or.inr ⟨σ', rfl, ?_⟩
        have hσσ' : σ <+: σ' := mem_cone.mp (Set.singleton_subset_iff.mp hX'X)
        have h2 : cone σ' ⊆ cone σ := cone_subset_cone.mpr hσσ'
        exact ((prepend_subset_cone σ' Y').trans (h2.trans hsub)).trans hZZ'
    · obtain rfl : X' = ({σ} : Set Str) := subset_singleton_eq hX' hX'X
      exact Or.inr ⟨σ, rfl, ((prepend_mono σ hY'Y).trans hsub).trans hZZ'⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
