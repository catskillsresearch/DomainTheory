/-ai
If one string is a prefix of another, then the doubled encoding of the first is a prefix of the doubled encoding of the second.

Write the longer string as the shorter string followed by a continuation. Doubling distributes over that concatenation, and the continuation of the encodings is the encoding of the continuation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_append

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

theorem enc_prefix_of_prefix {σ τ : Str} (h : σ <+: τ) : enc σ <+: enc τ := by
  obtain ⟨t, rfl⟩ := h
  rw [enc_append]
  exact ⟨enc t, rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
