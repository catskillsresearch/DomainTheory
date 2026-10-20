module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.coe_evalFin

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set








/-- **`denote e` via the `Finset` simulation.** `w` matches `e` iff some live state after reading
`w` is accepting — a decidable `Finset` intersection test. -/
theorem denote_iff_evalFin (e : SExpr) (w : List Bool) :
    w ∈ denote e ↔ (evalFin e w ∩ acceptFin e).Nonempty := by
  rw [← toNFA_accepts e]
  constructor
  · rintro ⟨s, hs, hse⟩
    refine ⟨s, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [← Finset.mem_coe, coe_evalFin]; exact hse
    · rw [← Finset.mem_coe, coe_acceptFin]; exact hs
  · rintro ⟨s, hs⟩
    rw [Finset.mem_inter] at hs
    obtain ⟨hs1, hs2⟩ := hs
    refine ⟨s, ?_, ?_⟩
    · rw [← Finset.mem_coe, coe_acceptFin] at hs2; exact hs2
    · rw [← Finset.mem_coe, coe_evalFin] at hs1; exact hs1

end Exercise722
end DomainTheory.NeighbourhoodSystems
