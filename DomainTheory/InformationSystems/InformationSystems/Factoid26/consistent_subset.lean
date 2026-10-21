/-ai
A subset of a consistent finite set is consistent.

Graph atoms of the subset already lie in the larger set, so consistency of the larger set equates their values.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Consistent

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid26

theorem consistent_subset {A B : Type*} {u v : Finset (Token A B)} (huv : v ⊆ u)
    (hu : Consistent u) : Consistent v :=
  fun _a _b _b' hb hb' => hu (huv hb) (huv hb')

end Factoid26

end DomainTheory.InformationSystems
