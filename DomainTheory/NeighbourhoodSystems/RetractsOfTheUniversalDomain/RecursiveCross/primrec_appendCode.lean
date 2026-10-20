module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.primrec_consStep2

@[expose] public section


namespace Domain.Recursive




theorem primrec_appendCode : Nat.Primrec (fun t => appendCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_consStep2 (Nat.Primrec.const 0) Nat.Primrec.right
    Nat.Primrec.left).of_eq fun _ => rfl

end Domain.Recursive
