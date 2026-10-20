module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace Factoid26



theorem consistent_empty {A B : Type*} :
    Consistent (∅ : Finset (Token A B)) := by
  intro _a _b _b' hb _
  exact False.elim (Finset.notMem_empty _ hb)

end Factoid26
end DomainTheory.InformationSystems
