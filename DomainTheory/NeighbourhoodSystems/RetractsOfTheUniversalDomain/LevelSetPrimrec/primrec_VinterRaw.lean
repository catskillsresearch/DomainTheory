/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLand
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myLand
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VinterRaw

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_VinterRaw : Nat.Primrec (fun t => VinterRaw t.unpair.1 t.unpair.2) := by
  have hcn : Nat.Primrec (fun t : ℕ => canonIdx t.unpair.1) := primrec_canonIdx.comp Nat.Primrec.left
  have hcm : Nat.Primrec (fun t : ℕ => canonIdx t.unpair.2) := primrec_canonIdx.comp Nat.Primrec.right
  have hk1 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.1).unpair.1) := Nat.Primrec.left.comp hcn
  have hm1 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.1).unpair.2) := Nat.Primrec.right.comp hcn
  have hk2 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2).unpair.1) := Nat.Primrec.left.comp hcm
  have hm2 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2).unpair.2) := Nat.Primrec.right.comp hcm
  have hkJ : Nat.Primrec (fun t : ℕ => max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) :=
    primrec_max hk1 hk2
  have hup1 : Nat.Primrec (fun t : ℕ => myUpsample (canonIdx t.unpair.1).unpair.1
      (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1)
      (canonIdx t.unpair.1).unpair.2) :=
    (primrec_myUpsample.comp (hk1.pair (hkJ.pair hm1))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hup2 : Nat.Primrec (fun t : ℕ => myUpsample (canonIdx t.unpair.2).unpair.1
      (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1)
      (canonIdx t.unpair.2).unpair.2) :=
    (primrec_myUpsample.comp (hk2.pair (hkJ.pair hm2))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hland : Nat.Primrec (fun t : ℕ => myLand
      (myUpsample (canonIdx t.unpair.1).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.1).unpair.2)
      (myUpsample (canonIdx t.unpair.2).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.2).unpair.2)) :=
    (primrec_myLand.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair hland).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
