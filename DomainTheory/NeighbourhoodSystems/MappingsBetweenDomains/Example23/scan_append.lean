module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_false

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Stability of the scan under extension.** Once `scan σ` has committed to a parity `some b`,
every extension `σ ++ t` keeps that value. This is the engine of monotonicity for `parityMap`. -/
theorem scan_append {σ : Str} {b : Bool} (h : scan σ = some b) (t : Str) :
    scan (σ ++ t) = some b := by
  induction σ generalizing b with
  | nil => simp at h
  | cons c σ₀ ih =>
    cases c with
    | true => simp only [scan_true] at h ⊢; exact h
    | false =>
      simp only [List.cons_append, scan_false] at h ⊢
      rw [Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [ih ha]
      rfl

end DomainTheory.NeighbourhoodSystems.Example23
