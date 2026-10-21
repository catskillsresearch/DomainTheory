/-ai
Scott 1976, (7.15) and (7.16). The combinator Z at a stage is the graph of the map sending a function to the graph of its iterator at that stage.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Z

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (7.15)–(7.16).** Combinators `Zₙ = λf λx. fⁿ(x)`. -/
def Zcomb (n : ℕ) : Pomega :=
  graph (fun f => graph (fun x => Z n f x))

end DomainTheory.DataTypesAsLattices
