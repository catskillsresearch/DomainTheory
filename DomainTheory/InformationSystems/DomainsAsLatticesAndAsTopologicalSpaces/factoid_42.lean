module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.familyInf

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem factoid_42 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x y : sys.Element),
      sys.familyInf ({x, y} : Set sys.Element) ⟨x, Set.mem_insert x {y}⟩ = sys.inf x y :=
  @familyInf.pair

end DomainTheory.InformationSystems.InfoSys
