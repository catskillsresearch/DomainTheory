/-ai
The universal domain is a subdomain of the solution domain, so the solution contains a copy of the universal domain.

The universal domain is a subdomain of its infinite power. That power is a subdomain of the fixed neighbourhood of the combinator, witnessed by the identity subsystem and the reverse of their isomorphism. That fixed neighbourhood is a subdomain of the function space from the solution into it, by the constant-function embedding. That function space is a subdomain of the solution, witnessed by the identity subsystem and the reverse of the solution isomorphism. Transitivity of the subdomain relation chains the four embeddings.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.fixedNbhd_cCombinator_isomorphic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.Dsol_isomorphic_funSpace_cCombinator

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap




















/-- **`𝒰 ⊴ D`**: the solution domain contains a copy of the universal domain `𝒰`, so it is
non-trivial (Scott's remark). Chains `𝒰 ⊴ 𝒰^∞` (`Exercise825Embed.trianglelefteq_iterSys`),
`𝒰^∞ ≅ fixedNbhd c`, the general constant-function embedding `𝒱 ⊴ (𝒟 → 𝒱)`
(`Exercise820.trianglelefteq_funSpace_const`), and `D → (fixedNbhd c) ≅ D`. -/
theorem U_trianglelefteq_Dsol : U ⊴ fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) := by
  set D := fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) with hD
  have h1 : U ⊴ iterSys U := trianglelefteq_iterSys U
  have h2 : iterSys U ⊴ fixedNbhd cCombinator :=
    ⟨fixedNbhd cCombinator, Subsystem.refl _, fixedNbhd_cCombinator_isomorphic.symm⟩
  have h3 : fixedNbhd cCombinator ⊴ funSpace D (fixedNbhd cCombinator) :=
    trianglelefteq_funSpace_const D (fixedNbhd cCombinator)
  have h4 : funSpace D (fixedNbhd cCombinator) ⊴ D :=
    ⟨D, Subsystem.refl D, Dsol_isomorphic_funSpace_cCombinator.symm⟩
  exact trianglelefteq_trans (trianglelefteq_trans (trianglelefteq_trans h1 h2) h3) h4

end DomainTheory.NeighbourhoodSystems
