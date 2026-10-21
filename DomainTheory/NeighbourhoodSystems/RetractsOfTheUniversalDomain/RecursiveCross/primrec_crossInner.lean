/-ai
If bop is primitive recursive, then the function sending a packed pair to crossInner bop of its two components is primitive recursive.

It is the primitive recursive fold of the inner step of bop, with the left projection, the constant zero, and the right projection, and that fold agrees with crossInner by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.primrec_crossInnerStep

@[expose] public section


namespace Domain.Recursive


theorem primrec_crossInner {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (fun t => crossInner bop t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_crossInnerStep hbop) Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq fun _ => rfl

end Domain.Recursive
