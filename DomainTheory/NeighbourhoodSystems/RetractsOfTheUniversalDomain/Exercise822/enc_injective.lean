module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_prefix_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

theorem enc_injective {σ τ : Str} (h : enc σ = enc τ) : σ = τ := by
  have h1 : σ <+: τ := enc_prefix_iff.mp ⟨[], by simpa using h⟩
  have h2 : τ <+: σ := enc_prefix_iff.mp ⟨[], by simpa using h.symm⟩
  exact h1.eq_of_length (h1.length_le.antisymm h2.length_le)

end Exercise822

end DomainTheory.NeighbourhoodSystems
