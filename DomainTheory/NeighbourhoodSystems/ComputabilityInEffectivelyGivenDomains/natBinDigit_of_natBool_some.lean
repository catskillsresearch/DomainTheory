module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem natBinDigit_of_natBool_some (n : ℕ) {b : Bool} (h : natBool n = some b) :
    n = 0 ∨ n = 1 := by
  match n with
  | 0 => simp [natBool] at h; exact Or.inl rfl
  | 1 => simp [natBool] at h; exact Or.inr rfl
  | n + 2 => simp [natBool] at h

end Exercise722

end DomainTheory.NeighbourhoodSystems
