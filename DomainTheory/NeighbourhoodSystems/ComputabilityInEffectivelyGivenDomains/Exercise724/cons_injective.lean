/-ai
Prepending is injective in the index and the sequence together: equal prepends have equal indices and equal underlying sequences.

Case on whether each sequence is finite or infinite. Two finite sequences give the index and the tail by injectivity of the list constructor. A finite sequence and an infinite sequence are distinct constructors. Two infinite sequences have equal stream-prepends; the value at 0 is the index, and the values at the positive positions are the tails.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Gamma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **`cons` is injective** (jointly in both arguments): `(i, γ) = (j, δ) ⟹ i = j ∧ γ = δ`. -/
theorem cons_injective {i j : ℕ} {γ δ : Gamma} (h : cons i γ = cons j δ) : i = j ∧ γ = δ := by
  cases γ with
  | inl l =>
    cases δ with
    | inl l' =>
      simp only [cons, Sum.inl.injEq, List.cons.injEq] at h
      exact ⟨h.1, by rw [h.2]⟩
    | inr s' => simp [cons] at h
  | inr s =>
    cases δ with
    | inl l' => simp [cons] at h
    | inr s' =>
      have heq : streamCons i s = streamCons j s' := by simpa [cons] using h
      have hi : i = j := by simpa using congrFun heq 0
      refine ⟨hi, ?_⟩
      have hs : s = s' := funext fun n => by simpa using congrFun heq (n + 1)
      rw [hs]

end DomainTheory.NeighbourhoodSystems.Exercise724
