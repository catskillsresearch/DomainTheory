module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.finiteApproximants

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem factoid_45 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x : sys.Element),
      x = sys.directedSup (sys.finiteApproximants x)
        (finiteApproximants.nonempty sys x) (finiteApproximants.directed sys x) :=
  @finiteApproximants.eq_directedSup

end DomainTheory.InformationSystems.InfoSys
