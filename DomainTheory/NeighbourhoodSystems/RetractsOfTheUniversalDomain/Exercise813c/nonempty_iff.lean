module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_evalSet'_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Corresponds

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- `Corresponds` matches `Set.Nonempty` — via `n ↦ fun i => n.testBit i` directly for `→`, and
`exists_bitsOf_agree` (`8.13(b)`) for `←`, since a formula's satisfying valuation can always be
swapped for a matching bit-derived one on its own (finite) variables. -/
theorem Corresponds.nonempty_iff {X : Set ℕ} {Y : Set (ℕ → Bool)} (h : Corresponds X Y) :
    X.Nonempty ↔ Y.Nonempty := by
  obtain ⟨φ, rfl, rfl⟩ := h
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨fun i => n.testBit i, (mem_evalSet'_iff _ φ).mpr ((mem_evalSet_iff n φ).mp hn)⟩
  · rintro ⟨v, hv⟩
    obtain ⟨n, hn⟩ := exists_bitsOf_agree (vars φ) v
    refine ⟨n, (mem_evalSet_iff n φ).mpr ?_⟩
    rw [evalV_eq_of_agree hn]
    exact (mem_evalSet'_iff v φ).mp hv

end DomainTheory.NeighbourhoodSystems
