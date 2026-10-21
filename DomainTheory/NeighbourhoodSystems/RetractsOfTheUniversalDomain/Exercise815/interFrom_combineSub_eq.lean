/-ai
If two lists are sublists of js, the intersection along their combination inside js equals the intersection of the two separate intersections along those sublists, all taken from the master neighbourhood.

Extensionality reduces the claim to membership. A point lies in an intersection when it lies in the master and in every selected basic neighbourhood. Membership in the combination is membership in js together with membership in one of the two sublists, so the combined condition splits into the two separate conditions and reassembles from them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.combineSub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_combineSub

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

section Combine

variable (js sub1 sub2 : List ℕ)

variable {js sub1 sub2}

/-- **Combining two consistent sub-meets.** If `sub1, sub2 ⊑ js`, then `interFrom P D.master
(combineSub js sub1 sub2) = interFrom P D.master sub1 ∩ interFrom P D.master sub2` — a pure
set-theoretic fact about `interFrom`'s membership characterization (no consistency needed here). -/
theorem interFrom_combineSub_eq (h1 : sub1.Sublist js) (h2 : sub2.Sublist js) :
    interFrom P D.master (combineSub js sub1 sub2) =
      interFrom P D.master sub1 ∩ interFrom P D.master sub2 := by
  apply Set.ext
  intro z
  rw [Set.mem_inter_iff, mem_interFrom, mem_interFrom, mem_interFrom]
  constructor
  · rintro ⟨hzm, hall⟩
    exact ⟨⟨hzm, fun j hj => hall j (mem_combineSub.mpr ⟨h1.subset hj, Or.inl hj⟩)⟩,
      hzm, fun j hj => hall j (mem_combineSub.mpr ⟨h2.subset hj, Or.inr hj⟩)⟩
  · rintro ⟨⟨hzm, hall1⟩, _, hall2⟩
    refine ⟨hzm, fun j hj => ?_⟩
    obtain ⟨_, hj1 | hj2⟩ := mem_combineSub.mp hj
    · exact hall1 j hj1
    · exact hall2 j hj2

end Combine

end FinGen

end DomainTheory.NeighbourhoodSystems
