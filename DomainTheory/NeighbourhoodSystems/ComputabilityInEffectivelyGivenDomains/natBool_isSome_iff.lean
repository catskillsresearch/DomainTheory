module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem natBool_isSome_iff (n : ℕ) :
    (natBool n).isSome = true ↔ n = 0 ∨ n = 1 := by
  match n with
  | 0 => simp [natBool]
  | 1 => simp [natBool]
  | n + 2 => simp [natBool]

end Exercise722

end DomainTheory.NeighbourhoodSystems
