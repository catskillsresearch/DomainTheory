/-ai
Inserting the least-informative token into a consistent finite set preserves consistency.

A graph atom in the enlarged set is distinct from the inserted least token, so both graph atoms already belong to the original set, and the original consistency equates their values.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Consistent

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid26

theorem consistent_insert_bot {A B : Type*} [DecidableEq A] [DecidableEq B]
    {u : Finset (Token A B)} (hu : Consistent u) :
    Consistent (insert (Token.bot : Token A B) u) := by
  intro a b b' hb hb'
  have hb1 : Token.pair a b ∈ u := by
    rcases Finset.mem_insert.mp hb with h | h
    · cases h
    · exact h
  have hb2 : Token.pair a b' ∈ u := by
    rcases Finset.mem_insert.mp hb' with h | h
    · cases h
    · exact h
  exact hu hb1 hb2

end Factoid26

end DomainTheory.InformationSystems
