module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

variable {σ : Type}

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

omit [Fintype σ] in
theorem mem_accepts_of_path {s t : σ} {x : List Bool} (hs : s ∈ M.start) (ht : t ∈ M.accept)
    (p : M.Path s t x) : x ∈ M.accepts := by
  rw [NFA.accepts_iff_exists_path]
  exact ⟨s, hs, t, ht, ⟨p⟩⟩

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems
