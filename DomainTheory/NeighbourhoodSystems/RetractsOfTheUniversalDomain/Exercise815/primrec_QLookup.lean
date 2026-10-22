module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QLookup

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

theorem primrec_QLookup (hr : Nat.Primrec r) : Nat.Primrec (QLookup r) := by
  have hleaf : Nat.Primrec (fun w : ℕ => r w.unpair.2.unpair.2) :=
    hr.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hleft : Nat.Primrec (fun w : ℕ => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0) :=
    (primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (Nat.Primrec.const 0)))).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hright : Nat.Primrec (fun w : ℕ => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0) :=
    (primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (Nat.Primrec.const 0)))).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnode : Nat.Primrec (fun w : ℕ =>
      Uinter (nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0)
        (nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0)) :=
    (Uinter_primrec.comp (hleft.pair hright)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have htag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hisone1 : Nat.Primrec (fun w : ℕ => isOne (1 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) htag)
  have hisone2 : Nat.Primrec (fun w : ℕ => isOne (2 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) htag)
  refine (primrec_selectFn hisone1 hleaf
    (primrec_selectFn hisone2 hnode (Nat.Primrec.const UComputablePresentation.masterIdx))).of_eq
    fun w => ?_
  show _ = QLookup r w
  unfold QLookup QBody
  match tag : w.unpair.2.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01' : (1 - 1 : ℕ) = 0 := rfl
    have h12' : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01', h12', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | t + 2 =>
    have h01' : (1 - (t + 2) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - (t + 2) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [h01', h12', isOne_zero, selectFn_zero]

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
