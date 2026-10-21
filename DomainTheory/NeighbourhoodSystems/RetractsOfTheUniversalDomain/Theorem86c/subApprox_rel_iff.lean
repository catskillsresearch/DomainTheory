/-ai
When F is a neighbourhood of the function space, the packaged map relates F to G exactly when G is a neighbourhood of the function space and contains sub of the least map of the principal neighbourhood of F.

One direction retains the membership of G and the containment. The other direction restores the given membership of F.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}


/-- **`subApprox`'s relation, unfolded via `ofMono`/`ofContinuous`/`toFilter`.** `F subApprox G`
holds iff `G` is a genuine function-space neighbourhood containing `sub` of `F`'s least map (any
witnessing proof `hF` of `F`'s membership works, by proof irrelevance). -/
theorem subApprox_rel_iff {F G : Set (ApproximableMap E E)} (hF : (funSpace E E).mem F) :
    (subApprox (E := E)).rel F G ↔
      (funSpace E E).mem G ∧ sub (toApproxMap ((funSpace E E).principal hF)) ∈ G :=
  ⟨fun ⟨_, hG, hmem⟩ => ⟨hG, hmem⟩, fun ⟨hG, hmem⟩ => ⟨hF, hG, hmem⟩⟩

end DomainTheory.NeighbourhoodSystems
