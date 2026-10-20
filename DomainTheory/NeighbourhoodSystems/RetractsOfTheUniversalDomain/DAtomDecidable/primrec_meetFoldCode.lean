module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.primrec_meetStepCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)








theorem primrec_meetFoldCode (hconsp : Nat.Primrec cons) :
    Nat.Primrec (meetFoldCode P cons) :=
  (primrec_foldCode (primrec_meetStepCode P cons hconsp) (Nat.Primrec.const 0)
    (Nat.Primrec.const (Nat.pair 1 P.masterIdx)) primrec_id).of_eq (fun _ => rfl)

end DomainTheory.NeighbourhoodSystems
