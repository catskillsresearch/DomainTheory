/-ai
The principal element on the terminator singleton of a finite binary string σ is a total element of the system C.

Let an element y lie above that principal element, and let Z belong to y. The singleton of σ belongs to y, so its intersection with Z belongs to y and is a neighbourhood of C. A neighbourhood of C contained in a singleton equals that singleton, so the intersection equals the singleton of σ. Hence Z is a neighbourhood of C, and rewriting the equality shows that the singleton is contained in Z.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Total finite sequences.** `↑{σ}` is a total (maximal) element of `|𝒞|`: any element above it
must equal it, because `{σ}` is a minimal nonempty neighbourhood. This is what was *false* in `𝔹`,
where finite sequences gave only the partial `σ⊥`. -/
theorem isTotal_singletonElt (σ : Str) : C.IsTotal (singletonElt σ) := by
  intro y hy Z hZ
  have hσy : y.mem ({σ} : Set Str) := hy {σ} ⟨memC_singleton σ, subset_rfl⟩
  have hinter : y.mem (({σ} : Set Str) ∩ Z) := y.inter_mem hσy hZ
  have hmemC : C.mem (({σ} : Set Str) ∩ Z) := y.sub hinter
  have heq : ({σ} : Set Str) ∩ Z = ({σ} : Set Str) :=
    subset_singleton_eq hmemC Set.inter_subset_left
  exact ⟨y.sub hZ, by rw [← heq]; exact Set.inter_subset_right⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
