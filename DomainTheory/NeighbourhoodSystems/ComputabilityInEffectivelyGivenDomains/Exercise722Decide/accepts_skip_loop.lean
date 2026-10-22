module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathAppend
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathAppend_take_drop
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.mem_accepts_of_path

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
theorem accepts_skip_loop {s t : σ} {x : List Bool} {i j : ℕ}
    (hi : i ≤ x.length) (hj : j ≤ x.length) (_hij : i < j)
    (hs : s ∈ M.start) (ht : t ∈ M.accept) (hp : M.Path s t x)
    (heq : pathStateAt hp i hi = pathStateAt hp j hj) :
    x.take i ++ x.drop j ∈ M.accepts := by
  let splitI := pathAppend_take_drop hp i hi
  let splitJ := pathAppend_take_drop hp j hj
  have hqq' : splitI.u = splitJ.u := by rw [← splitI.hu, heq, splitJ.hu]
  exact mem_accepts_of_path hs ht (pathAppend splitI.hp (hqq' ▸ splitJ.ht))

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems
