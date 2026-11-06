module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.eq_directedSup_finiteApproximants

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_45 :
    ∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x : sys.Element),
      x = sys.directedSup (sys.finiteApproximants x)
        (sys.nonempty_finiteApproximants x) (sys.directed_finiteApproximants x) :=
  @eq_directedSup_finiteApproximants

end DomainTheory.InformationSystems.InfoSys
