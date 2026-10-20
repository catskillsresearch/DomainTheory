module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The pointwise **meet** `⋀ 𝒮` of a family of approximable maps (drawn from `C`): `X (⋀𝒮) Y` iff
`(X, Y)` lies in every member of `𝒮`. -/
def meetMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁) (hne : 𝒮.Nonempty) :
    ApproximableMap V₀ V₁ where
  rel X Y := ∀ S ∈ 𝒮, (X, Y) ∈ S
  rel_dom := by
    intro X Y h
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.rel_dom (h _ hS)
  rel_cod := by
    intro X Y h
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.rel_cod (h _ hS)
  master_rel := by
    intro S hS; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.master_rel
  inter_right := by
    intro X Y Y' hY hY' S hS
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.inter_right (hY _ hS) (hY' _ hS)
  mono := by
    intro X X' Y Y' h hX'X hYY' hX' hY' S hS
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.mono (h _ hS) hX'X hYY' hX' hY'

end DomainTheory.NeighbourhoodSystems.Exercise327
