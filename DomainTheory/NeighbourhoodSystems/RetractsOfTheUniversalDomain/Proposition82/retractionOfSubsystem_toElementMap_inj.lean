/-ai
The subsystem retraction fixes the image of every subsystem element under the injection.

The action of the retraction on that image is the injection of the projection of the image. The projection of the image is the composite of the projection after the injection, which is the identity, so the element map of the identity returns the element and injecting it restores the image.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition81
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem_rel

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_comp_inj
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem

/-- `retractionOfSubsystem h` fixes exactly `i(x)` for `x ∈ |D|`: `a(i(x)) = i(x)`. -/
theorem retractionOfSubsystem_toElementMap_inj (h : D ◁ E) (x : D.Element) :
    (retractionOfSubsystem h).toElementMap (h.inj.toElementMap x) = h.inj.toElementMap x := by
  have h1 : (retractionOfSubsystem h).toElementMap (h.inj.toElementMap x)
      = h.inj.toElementMap (h.proj.toElementMap (h.inj.toElementMap x)) :=
    toElementMap_comp h.inj h.proj (h.inj.toElementMap x)
  have h2 : h.proj.toElementMap (h.inj.toElementMap x) = (h.proj.comp h.inj).toElementMap x :=
    (toElementMap_comp h.proj h.inj x).symm
  rw [h1, h2, h.proj_comp_inj, toElementMap_idMap]

end Subsystem

end DomainTheory.NeighbourhoodSystems
