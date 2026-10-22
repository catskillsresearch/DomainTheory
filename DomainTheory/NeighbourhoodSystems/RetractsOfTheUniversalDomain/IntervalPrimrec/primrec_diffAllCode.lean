module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.primrec_diffAllStep

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_diffAllCode : Nat.Primrec (fun t : ℕ => diffAllCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_diffAllStep (Nat.Primrec.const 0)
    (Nat.Primrec.succ.comp (Nat.Primrec.left.pair (Nat.Primrec.const 0)))
    Nat.Primrec.right).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
