/-ai
For positive n, if every component of a tagged tuple belongs to MemA and the tuple is contained in a tuple of another tag, then the two tags agree.

Take a nonempty witness in the component at index zero, send its prefixed word into the larger tuple, and read the tag from uniqueness of slot prefixes.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slotPre_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

/-- A non-empty witness contained in a tag-`i'` tuple must carry the tag `i'`. -/
theorem tag_eq_of_subset (hn : 0 < n) {i i' : Bool} {Z V : Fin n → Set Str}
    (hZ : ∀ j, MemA n (Z j)) (hsub : embTuple i Z ⊆ embTuple i' V) : i = i' := by
  obtain ⟨a, ha⟩ := memA_nonempty hn (hZ ⟨0, hn⟩)
  obtain ⟨j', v, he, -⟩ := hsub ⟨⟨0, hn⟩, a, rfl, ha⟩
  exact (slotPre_inj he).1

end Example62A

end DomainTheory.NeighbourhoodSystems
