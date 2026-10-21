/-ai
The index-continuous environment update of t by x along an index is the minimal extension of the map sending each n to the update of t by x at n. On a singleton numeral this is the single update, and on a larger index it is the union of the corresponding updates.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Environment update continuous in the index: on `n = {n}` this is
`t[x/n]`; on a larger index it unions the corresponding updates. -/
def updateEnvUnion (t x idx : Pomega) : Pomega :=
  minExtend (fun n => updateEnv t x n) idx

end DomainTheory.DataTypesAsLattices
