module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInf_pair

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_42 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x y : sys.Element),
      sys.familyInf ({x, y} : Set sys.Element) ⟨x, Set.mem_insert x {y}⟩ = sys.inf x y :=
  @familyInf_pair

end DomainTheory.InformationSystems.InfoSys
