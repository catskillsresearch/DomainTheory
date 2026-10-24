module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.vars
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.SemanticEquiv
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Lindenbaum
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.toSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Entails
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.mem_evalSet_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV_eq_of_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.exists_bitsOf_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.formulaSetoid
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.semanticEquiv_iff_evalSet_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.toSet_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.generatedBy_iff_exists_evalSet

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


/-- **Headline: `Lindenbaum.toSet`'s range is exactly `Exercise813a.lean`'s free Boolean algebra on
`ℵ₀` generators, `{X | GeneratedBy generator X}`.** Together with injectivity, `Lindenbaum.toSet`
is a bijection `Lindenbaum ≃ {X : Set ℕ // GeneratedBy generator X}` — i.e. `Lindenbaum` *is* (a
faithful copy of) the algebra `8.13(a)` already showed `U ≅ᴰ`'s domain of proper filters is built
from. This is exactly `8.13`'s parenthetical: "the free Boolean algebra on `ℵ₀`-generators
(= the Lindenbaum algebra of propositional calculus)." -/
theorem Lindenbaum.range_toSet : Set.range Lindenbaum.toSet = {X | GeneratedBy generator X} := by
  ext X
  simp only [Set.mem_range, Set.mem_ofPred_eq, generatedBy_iff_exists_evalSet]
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.ind with
    | _ φ => exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨⟦φ⟧, rfl⟩

end DomainTheory.NeighbourhoodSystems
