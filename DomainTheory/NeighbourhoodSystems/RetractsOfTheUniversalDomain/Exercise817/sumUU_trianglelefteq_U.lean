module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.Basic

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}


/-- **Exercise 8.17, Part 1 (`+`).** `iPlus/jPlus` (`Definition89.lean`) already *are* the computable
projection pair `𝒰+𝒰 ⇄ 𝒰` needed for 8.9. Bonus: Lemma 6.15 upgrades it to `𝒰+𝒰 ⊴ 𝒰`. -/
theorem sumUU_trianglelefteq_U : sum U U U_mem_nonempty U_mem_nonempty ⊴ U :=
  trianglelefteq_of_projectionPair iPlus jPlus jPlus_comp_iPlus iPlus_comp_jPlus_le

end DomainTheory.NeighbourhoodSystems
