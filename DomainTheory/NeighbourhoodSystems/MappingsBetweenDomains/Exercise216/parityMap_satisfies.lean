/-ai
The parity map satisfies the three parity equations.

Each equation compares neighbourhood membership through the shift formula for the parity map on a prefixed element. For a leading one, and for a leading zero followed by one, the corresponding scan rule fixes the value of the concatenation, and the empty string together with the master neighbourhood supplies the converse witness. For a leading pair of zeros, the scan of a double zero and the membership formula for the parity map transport witnesses in both directions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise216.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`parityMap` satisfies its own defining equations.** Each is a direct instance of the
"shift formula" `Example23.parityMap_toElementMap_sigmaElt`, using that a leading `1` (resp. `01`,
`00`) fixes the scan of the concatenation `σ ++ τ` regardless of the tail `τ`
(`scan_append_true`/`scan_append_falseTrue`/`scan_append_falseFalse`). -/
theorem parityMap_satisfies : SatisfiesParityEquations Example23.parityMap where
  one x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_true] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_true]⟩
  zeroOne x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_falseTrue] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_falseTrue]⟩
  zeroZero x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt, Example23.parityMap_toElementMap_mem]
    constructor
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse] at hval⟩
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse]⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
