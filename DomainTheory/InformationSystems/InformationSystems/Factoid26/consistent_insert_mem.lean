module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Consistent

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid26

theorem consistent_insert_mem {A B : Type*} [DecidableEq A] [DecidableEq B]
    {u : Finset (Token A B)} {t : Token A B}
    (ht : t ∈ u) (hu : Consistent u) : Consistent (insert t u) := by
  simpa [Finset.insert_eq_of_mem ht] using hu

end Factoid26

end DomainTheory.InformationSystems
