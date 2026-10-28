module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInfCarrier
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInf
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.le_familyInf

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_inf
@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem familyInf_pair (x y : sys.Element) :
    sys.familyInf ({x, y} : Set sys.Element) ⟨x, Set.mem_insert x {y}⟩ = sys.inf x y := by
  refine le_antisymm ?_ ?_
  · exact sys.le_inf
      (familyInf.le sys _ _ (Set.mem_insert x {y}))
      (familyInf.le sys _ _ (Set.mem_insert_of_mem _ rfl))
  · apply sys.le_familyInf
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hy
    · exact inf.le_left sys _ _
    · have : z = y := hy
      subst this
      exact inf.le_right sys _ _

end InfoSys
end DomainTheory.InformationSystems
