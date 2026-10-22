module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strct

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem strct_mono : Monotone (strct (V₀ := V₀) (V₁ := V₁)) := by
  intro a b hab W hW
  obtain ⟨hWmem, haW⟩ := hW
  obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
  refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
  intro p hp
  have hle : toApproxMap a ≤ toApproxMap b := (funSpaceEquiv V₀ V₁).monotone hab
  exact ⟨hle p.1 p.2 (haW p hp).1, (haW p hp).2⟩

end Part5

end Exercise627

end DomainTheory.NeighbourhoodSystems
