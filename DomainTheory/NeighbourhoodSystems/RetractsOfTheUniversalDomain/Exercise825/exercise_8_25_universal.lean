module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Unit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.U_trianglelefteq_Dsol
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

/-- **Exercise 8.25 (Scott 1981, PRG-19), non-triviality/universality.** The solution domain `D`
of `exercise_8_25` contains a genuine embedded copy of the universal domain `𝒰` (`𝒰 ⊴ D`), so it is
certainly not the one-point domain, and is in fact universal: every countable neighbourhood system
embeds (up to isomorphism) into `𝒰`, hence into `D`. -/
theorem exercise_8_25_universal : U ⊴ fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) :=
  U_trianglelefteq_Dsol

end DomainTheory.NeighbourhoodSystems
