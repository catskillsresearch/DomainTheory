module


public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAtAux
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}

variable {σ : Type}

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}


structure PathSplit {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ) (hn : n ≤ x.length) where
  u : σ
  hp : M.Path s u (x.take n)
  ht : M.Path u t (x.drop n)
  hu : pathStateAt p n hn = u

end Exercise722
end DomainTheory.NeighbourhoodSystems
