/-ai
If the depth of the intersection of two S-expressions is at most the fuel, the consistency character of their Gödel codes equals 1 exactly when the denotation of that intersection is nonempty.

Rewrite the consistency character as the nonemptiness character of the Gödel code of the intersection, and apply the characterization of that character.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic

@[expose] public section


namespace Domain.Recursive


open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


theorem consistentBChar_eq_one_iff {fuel : ℕ} {a b : SExpr}
    (h : c9b5_sexprDepth (.cap a b) ≤ fuel) :
    consistentBChar fuel (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b) = 1 ↔
      (denote (.cap a b)).Nonempty := by
  simp only [consistentBChar, ← c9b6_sexprGodelEncode_cap]
  exact decideNonemptyBChar_eq_one_iff h

end Domain.Recursive
