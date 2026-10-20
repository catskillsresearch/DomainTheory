module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- Decode with an explicit fuel bound so the recursion is structural. -/
def sexprOfNatFuel : ℕ → ℕ → Option SExpr
  | 0, _ => none
  | fuel + 1, n =>
    match n.unpair.1 with
    | 0 => some .sigma
    | 1 => (Encodable.decode n.unpair.2).map SExpr.single
    | 2 =>
      match sexprOfNatFuel fuel n.unpair.2.unpair.1, sexprOfNatFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none
    | 3 =>
      match sexprOfNatFuel fuel n.unpair.2.unpair.1, sexprOfNatFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none
    | _ => none

end Exercise722

end DomainTheory.NeighbourhoodSystems
