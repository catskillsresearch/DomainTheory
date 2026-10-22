module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

/-- **The key inclusion law:** `Sₙ ⊆ Sₖ ↔ INCL(n, k)`. `→` reads off `INCL(n, k)` from `n ∈ Sₙ`
(reflexivity (i)); `←` is transitivity (ii). -/
theorem toNbhd_subset_iff {n k : ℕ} : I.toNbhd n ⊆ I.toNbhd k ↔ I.INCL n k := by
  constructor
  · intro h
    exact h (I.incl_refl n)
  · intro hnk m hm
    exact I.incl_trans hm hnk

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
