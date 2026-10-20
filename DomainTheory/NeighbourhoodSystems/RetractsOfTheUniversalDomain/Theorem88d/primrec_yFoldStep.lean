module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_unionUX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.primrec_atomUEmpty

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)




















































theorem primrec_yFoldStep : Nat.Primrec (yFoldStep P) := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h2n : Nat.Primrec (fun w : ℕ => 2 ^ w.unpair.1) := primrec_two_pow hn
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 + 2 ^ w.unpair.1) :=
    primrec_add₂ hi h2n
  have hn1 : Nat.Primrec (fun w : ℕ => w.unpair.1 + 1) := Nat.Primrec.succ.comp hn
  have hempty : Nat.Primrec (fun w : ℕ =>
      atomUEmpty P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUEmpty P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcode : Nat.Primrec (fun w : ℕ =>
      atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUCode P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hfound : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hunion : Nat.Primrec (fun w : ℕ => unionUX w.unpair.2.unpair.2.unpair.2
      (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))) :=
    (primrec_unionUX.comp (hval.pair hcode)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun w : ℕ => selectFn w.unpair.2.unpair.2.unpair.1
      (Nat.pair 1 (unionUX w.unpair.2.unpair.2.unpair.2
        (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))))
      (Nat.pair 1 (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)))) :=
    primrec_selectFn hfound
      ((Nat.Primrec.const 1).pair hunion)
      ((Nat.Primrec.const 1).pair hcode)
  exact (primrec_selectFn hempty hacc hinner).of_eq fun w => by unfold yFoldStep; simp only []

end DomainTheory.NeighbourhoodSystems
