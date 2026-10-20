module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition81
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.isRetraction_retractionOfSubsystem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem





/-- **Proposition 8.2 (Scott 1981, PRG-19), packaged.** `D ◁ E` induces a retraction `a` on `E`
whose fixed-point set is (order-isomorphic to) `|D|`. -/
theorem retraction_of_subsystem (h : D ◁ E) :
    IsRetraction (retractionOfSubsystem h) ∧
      Nonempty (D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y}) :=
  ⟨isRetraction_retractionOfSubsystem h, ⟨elementIso h⟩⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems
