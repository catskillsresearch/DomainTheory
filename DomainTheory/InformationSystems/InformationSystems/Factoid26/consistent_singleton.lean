/-ai
Every singleton token set is consistent.

Both graph atoms extracted from the singleton equal the unique token. If that token is least-informative, the equality with a graph atom is impossible. If it is a graph atom, the two equalities identify the values.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Consistent

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid26

theorem consistent_singleton {A B : Type*} [DecidableEq A] [DecidableEq B]
    (t : Token A B) : Consistent ({t} : Finset (Token A B)) := by
  intro a b b' hb hb'
  rw [Finset.mem_singleton] at hb hb'
  -- both equal `t`; cases on `t`
  cases t with
  | bot =>
    cases hb
  | pair a0 b0 =>
    cases hb
    cases hb'
    rfl

end Factoid26

end DomainTheory.InformationSystems
