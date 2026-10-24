module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_14

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise115
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/- concordance: source L458 EXERCISE 1.15 finite elements without chains -/
/-- **Exercise 1.15.** `flat` and `stem` are *not* isomorphic: an order-isomorphism would transport
`stem`'s strict 3-chain `⊥ ⊏ ↑{0,1} ⊏ ↑{0}` back to a strict 3-chain in `flat`, which has none. -/
theorem not_isomorphic : ¬ (flat ≅ᴰ stem) := by
  rintro ⟨e⟩
  obtain ⟨a, b, c, hab, hbc⟩ := stem_three_chain
  exact flat_no_three_chain
    ⟨e.symm a, e.symm b, e.symm c, e.symm.lt_iff_lt.mpr hab, e.symm.lt_iff_lt.mpr hbc⟩

section
set_option linter.unusedVariables false

theorem example_115 : Not
  (@DomainTheory.NeighbourhoodSystems.Isomorphic Nat Nat DomainTheory.NeighbourhoodSystems.Exercise115.flat
    DomainTheory.NeighbourhoodSystems.Exercise115.stem) :=
  DomainTheory.NeighbourhoodSystems.Exercise115.not_isomorphic
end
end

end DomainTheory.NeighbourhoodSystems.Exercise115
end
