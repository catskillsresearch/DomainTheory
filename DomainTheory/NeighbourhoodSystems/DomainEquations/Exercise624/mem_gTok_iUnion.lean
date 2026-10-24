module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.fTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Dsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Esol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Fsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Gsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_gTok

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624


/-- **Additivity of `gTok`.** Every token of `gTok (⋃ₙ aₙ) (⋃ₙ bₙ)` already lies in some
`gTok aₙ bₙ` — each token references at most one coordinate. -/
theorem mem_gTok_iUnion {a b : ℕ → Set Str} {w : Str}
    (hw : w ∈ gTok (⋃ n, a n) (⋃ n, b n)) : ∃ n, w ∈ gTok (a n) (b n) := by
  rcases hw with rfl | ⟨w', rfl, hw'⟩ | ⟨w', rfl, hw'⟩
  · exact ⟨0, nil_mem_gTok _ _⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inl ⟨w', rfl, hn⟩)⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inr ⟨w', rfl, hn⟩)⟩

end Exercise624
end DomainTheory.NeighbourhoodSystems
