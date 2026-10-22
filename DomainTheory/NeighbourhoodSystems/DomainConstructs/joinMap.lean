module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The **join** `⋁ 𝒮` of a directed family of approximable maps: `X (⋁𝒮) Y` iff `(X, Y)` lies in
some member. Directedness is what restores the intersectivity condition (ii). -/
def joinMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁) (hne : 𝒮.Nonempty)
    (hdir : DirectedOn (· ⊆ ·) 𝒮) : ApproximableMap V₀ V₁ where
  rel X Y := ∃ S ∈ 𝒮, (X, Y) ∈ S
  rel_dom := by rintro X Y ⟨S, hS, hp⟩; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.rel_dom hp
  rel_cod := by rintro X Y ⟨S, hS, hp⟩; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.rel_cod hp
  master_rel := by
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact ⟨graph f, hS, f.master_rel⟩
  inter_right := by
    rintro X Y Y' ⟨S, hS, hp⟩ ⟨S', hS', hp'⟩
    obtain ⟨S₃, hS₃, hSS₃, hS'S₃⟩ := hdir S hS S' hS'
    obtain ⟨f, rfl⟩ := h𝒮 hS₃
    exact ⟨graph f, hS₃, f.inter_right (hSS₃ hp) (hS'S₃ hp')⟩
  mono := by
    rintro X X' Y Y' ⟨S, hS, hp⟩ hX'X hYY' hX' hY'
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact ⟨graph f, hS, f.mono hp hX'X hYY' hX' hY'⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
