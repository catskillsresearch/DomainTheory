module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.primrec_flatMapStep

@[expose] public section


namespace Domain.Recursive


theorem primrec_flatMapCode {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.Primrec (fun t => flatMapCode f t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_flatMapStep hf) Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq fun _ => rfl

end Domain.Recursive
