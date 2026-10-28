module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_23
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition_6_13

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
section
namespace Exercise624

theorem exists_simultaneous_subsystems :
    ∃ D E : ScottSys, D.sys ◁ (D.sum (D.prod E)).sys ∧ E.sys ◁ (D.sum E).sys :=
  ⟨Dsol, Esol, Dsol_subsystem, Esol_subsystem⟩

end Exercise624
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise624
section
set_option linter.unusedVariables false

theorem example_624 : ∃ (D : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys) (E :
  DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys),
  And
    (@DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str D.sys
      (D.sum (D.prod E)).sys)
    (@DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str E.sys (D.sum E).sys) :=
  DomainTheory.NeighbourhoodSystems.Exercise624.exists_simultaneous_subsystems
end

end DomainTheory.NeighbourhoodSystems.Exercise624
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

def liftTokMaster (D : NeighborhoodSystem Str) : Set Str := insert [] (embBit false D.master)

theorem embF_subset_liftTokMaster {X : Set Str} (hX : D.mem X) :
    embBit false X ⊆ liftTokMaster D :=
  (embBit_subset.mpr (D.sub_master hX)).trans (Set.subset_insert _ _)

theorem liftTokMaster_inter_embF {X : Set Str} (hX : D.mem X) :
    liftTokMaster D ∩ embBit false X = embBit false X :=
  Set.inter_eq_right.mpr (embF_subset_liftTokMaster hX)

theorem nil_mem_liftTokMaster : ([] : Str) ∈ liftTokMaster D := Set.mem_insert _ _

theorem embF_ne_liftTokMaster {X : Set Str} : embBit false X ≠ liftTokMaster D := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_liftTokMaster)

end Exercise619
end
end DomainTheory.NeighbourhoodSystems
end
