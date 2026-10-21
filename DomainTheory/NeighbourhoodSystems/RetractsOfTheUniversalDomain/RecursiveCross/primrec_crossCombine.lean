/-ai
If bop is primitive recursive, then the function sending a packed pair to crossCombine bop of its two components is primitive recursive.

It is the primitive recursive fold of the outer step of bop, with the right projection, the constant zero, and the left projection, and that fold agrees with crossCombine by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.primrec_crossOuterStep

@[expose] public section


namespace Domain.Recursive


theorem primrec_crossCombine {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (fun t => crossCombine bop t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_crossOuterStep hbop) Nat.Primrec.right (Nat.Primrec.const 0)
    Nat.Primrec.left).of_eq fun _ => rfl

end Domain.Recursive
