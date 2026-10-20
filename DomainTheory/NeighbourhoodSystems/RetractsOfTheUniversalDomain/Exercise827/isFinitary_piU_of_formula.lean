module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitary_piU_of_isFinitary_piD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitaryProjection_piD_of_formula

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap






































/-- **Exercise 8.27(b)(1), assembled with (b)(0):** formula (ii) for `piD d` alone gives
`IsFinitary (piU d)`, i.e. (combined with the already-Pass 8.27(a)) the *entire* exercise for `d`
polymorphic. This pins down exactly what Exercise 8.27(b)(2)–(b)(3) need to supply: `hii`. -/
theorem isFinitary_piU_of_formula {d : ApproximableMap U U}
    (hii : ∀ (x : (funSpace U U).Element) {Y}, ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) :
    IsFinitary (piU d) :=
  isFinitary_piU_of_isFinitary_piD (isFinitaryProjection_piD_of_formula d hii).2

end DomainTheory.NeighbourhoodSystems
