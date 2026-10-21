/-ai
A neighbourhood belongs to the parity map at the element obtained by prepending a string to an element exactly when some cone of the element has that neighbourhood in the element selected by scanning the concatenation.

From a membership witness, the inner neighbourhood is a cone and the cone inclusion is a prefix of the concatenation, so monotonicity of the scanned value moves the membership to the concatenated scan. Conversely the cone of the concatenation belongs to the shifted element by the prepend inclusion, and its scan is a witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **The "shift formula" for `parityMap`.** Reading off the parity of `σx` depends on `x` only
through *some* cone `cone τ ∈ x`, via the scan of the concatenation `σ ++ τ`: any deeper cone in
`sigmaElt`'s built-in up-closure is subsumed by monotonicity (`valElt_scan_mono`), so the longest
one — `σ ++ τ` itself — already witnesses the answer. This is the key computation behind Exercise
2.16's second half: `parityMap` genuinely satisfies its own defining equations. -/
theorem parityMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ (valElt (scan (σ ++ τ))).mem Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hval⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, valElt_scan_mono (cone_subset_cone.mp hsub) Y hval⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩, σ ++ τ, rfl, hval⟩

end DomainTheory.NeighbourhoodSystems.Example23
