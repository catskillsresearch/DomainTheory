/-ai
The fuelled decoder returns nothing when the fuel is zero. With fuel remaining, it unpairs the code. Tag 0 yields sigma when the payload is zero and nothing otherwise. Tag 1 yields the singleton of the decoded boolean list. Tag 2 yields the concatenation of the two fuelled decodings of the payload pair when both succeed. Tag 3 yields their intersection in the same way. Any other tag yields nothing.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Fuelled decoder: `fuel` bounds recursive unfoldings. -/
def decodeFuel (fuel : ℕ) (n : ℕ) : Option SExpr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match n.unpair.1 with
    | 0 => if n.unpair.2 = 0 then some .sigma else none
    | 1 => (decodeListBool n.unpair.2).map (.single ·)
    | 2 =>
      match decodeFuel fuel n.unpair.2.unpair.1, decodeFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none
    | 3 =>
      match decodeFuel fuel n.unpair.2.unpair.1, decodeFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none
    | _ => none

end Exercise722

end DomainTheory.NeighbourhoodSystems
