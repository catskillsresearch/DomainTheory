module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom_eq_empty_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace diff

open NeighborhoodSystem

theorem mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hdiff : D.DiffClosed)
    {A B : Set γ} (hA : A = ∅ ∨ D.mem A) (hB : D.mem B) : A \ B = ∅ ∨ D.mem (A \ B) := by
  rcases hA with rfl | hA
  · exact Or.inl (Set.empty_sdiff B)
  · exact hdiff hA hB

end diff
end DomainTheory.NeighbourhoodSystems
