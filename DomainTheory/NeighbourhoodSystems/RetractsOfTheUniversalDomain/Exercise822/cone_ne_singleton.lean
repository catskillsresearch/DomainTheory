module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

theorem cone_ne_singleton (σ τ : Str) : cone σ ≠ ({τ} : Set Str) := by
  intro h
  have h1 : σ ∈ cone σ := List.prefix_rfl
  have h2 : σ ++ [true] ∈ cone σ := ⟨[true], rfl⟩
  rw [h] at h1 h2
  simp only [Set.mem_singleton_iff] at h1 h2
  exact absurd (h2.trans h1.symm) (by simp)

end Exercise822

end DomainTheory.NeighbourhoodSystems
