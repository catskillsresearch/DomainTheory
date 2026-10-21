/-ai
The injection composed after the projection is contained in the identity on E. The projection composed after the injection equals the identity on D.

The numbered name theorem_612 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj_comp_proj_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_comp_inj

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Subsystem

set_option linter.unusedVariables false

theorem theorem_612.{u_1} : And
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E D E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α D E D
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D)) :=
  @And.intro
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E D E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α D E D
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D))
  @DomainTheory.NeighbourhoodSystems.Subsystem.inj_comp_proj_le
  @DomainTheory.NeighbourhoodSystems.Subsystem.proj_comp_inj

end DomainTheory.NeighbourhoodSystems.Subsystem
