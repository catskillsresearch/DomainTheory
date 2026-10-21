/-ai
A consistency presentation of a neighbourhood system is an enumeration of its neighbourhoods such that every enumerated set is a neighbourhood, every neighbourhood occurs in the enumeration, and consistency of two indices is recursively decidable. Consistency means that some enumerated neighbourhood is contained in the intersection of the two enumerated neighbourhoods. This is Definition 7.1 restricted to that consistency relation, without a decidable test for equality of an intersection with a third neighbourhood.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722

open Set Domain.Recursive

/-- Definition 7.1 restricted to relation (ii) only (no `interEq_computable`, unlike
`ComputablePresentation`/`ScottPresentation` in `Definition71.lean`/`Exercise715.lean`, whose
pattern this mirrors). -/
structure ConsistencyPresentation (V : NeighborhoodSystem α) where
  /-- The enumeration `𝒟 = {Xₙ ∣ n ∈ ℕ}`. -/
  X : ℕ → Set α
  /-- Every `Xₙ` is a neighbourhood. -/
  mem_X : ∀ n, V.mem (X n)
  /-- The enumeration is onto `𝒟`. -/
  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y
  /-- **7.1(ii)** — consistency `∃ k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable in `n, m`. -/
  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)

end Exercise722
end DomainTheory.NeighbourhoodSystems
