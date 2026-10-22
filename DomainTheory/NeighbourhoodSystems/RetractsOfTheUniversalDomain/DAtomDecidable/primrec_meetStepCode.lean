module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable (cons : ℕ → ℕ)


theorem primrec_meetStepCode (hconsp : Nat.Primrec cons) : Nat.Primrec (meetStepCode P cons) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hr : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hrok : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) := Nat.Primrec.left.comp hr
  have hridx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp hr
  have hconstest : Nat.Primrec (fun w : ℕ => cons (Nat.pair w.unpair.2.unpair.1.unpair.2 w.unpair.1)) :=
    hconsp.comp (hridx.pair hx)
  have hcond : Nat.Primrec
      (fun w : ℕ => isOne w.unpair.2.unpair.1.unpair.1 * isOne
        (cons (Nat.pair w.unpair.2.unpair.1.unpair.2 w.unpair.1))) :=
    primrec_mul₂ (primrec_isOne.comp hrok) (primrec_isOne.comp hconstest)
  have hinter : Nat.Primrec
      (fun w : ℕ => P.inter w.unpair.2.unpair.1.unpair.2 w.unpair.1) :=
    (P.inter_primrec.comp (hridx.pair hx)).of_eq
      (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hthen : Nat.Primrec
      (fun w : ℕ => Nat.pair 1 (P.inter w.unpair.2.unpair.1.unpair.2 w.unpair.1)) :=
    (Nat.Primrec.const 1).pair hinter
  have helse : Nat.Primrec (fun w : ℕ => Nat.pair 0 w.unpair.2.unpair.1.unpair.2) :=
    (Nat.Primrec.const 0).pair hridx
  exact (primrec_selectFn hcond hthen helse).of_eq (fun _ => rfl)

end DomainTheory.NeighbourhoodSystems
