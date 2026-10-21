/-ai
The choice-free binary union of finite sets u and v is the fold of insertion over the underlying multiset of v, starting from u. It has the same elements as the ordinary union and does not depend on classical choice.
ai-/
module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.instLeftCommutativeInsert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

/-- Choice-free binary union of finite sets, obtained by folding `insert` over the second
argument's underlying multiset. Definitionally equal in content to `u ∪ v`, but — unlike
mathlib's `(· ∪ ·)` — free of any `Classical.choice` dependency. -/
def funion (u v : Finset α) : Finset α := Multiset.foldr insert u v.1

end DomainTheory.InformationSystems.Constructive
