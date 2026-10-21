/-ai
If one string is a prefix of another, the element selected by scanning the shorter string lies below the element selected by scanning the longer string.

Write the longer string as the shorter one followed by a tail. If the shorter scan is none, its value is bottom, which lies below every element. If the shorter scan is a boolean, appending the tail leaves the scan unchanged, so the values agree.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.valElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.botElt_le
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_append

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Monotonicity of the parity value.** A longer prefix `σ <+: σ'` yields a (weakly) more defined
value: `valElt (scan σ) ⊑ valElt (scan σ')`. If `scan σ = none` then `valElt = ⊥ ⊑ _`; otherwise the
value is fixed by `scan_append`. -/
theorem valElt_scan_mono {σ σ' : Str} (h : σ <+: σ') :
    valElt (scan σ) ≤ valElt (scan σ') := by
  obtain ⟨t, rfl⟩ := h
  cases hσ : scan σ with
  | none => simpa [valElt, hσ] using botElt_le _
  | some b => rw [scan_append hσ t]

end DomainTheory.NeighbourhoodSystems.Example23
