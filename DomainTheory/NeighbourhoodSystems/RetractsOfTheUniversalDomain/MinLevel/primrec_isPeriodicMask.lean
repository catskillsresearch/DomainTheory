module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_isPeriodicMask :
    Nat.Primrec (fun t => isPeriodicMask t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hj : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hmodj : Nat.Primrec (fun t : ℕ => myModPow2 t.unpair.2.unpair.2 (2 ^ t.unpair.2.unpair.1)) :=
    (primrec.myModPow2.comp (hm.pair (primrec_two_pow hj))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hmodk : Nat.Primrec (fun t : ℕ => myModPow2 t.unpair.2.unpair.2 (2 ^ t.unpair.1)) :=
    (primrec.myModPow2.comp (hm.pair (primrec_two_pow hk))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hups : Nat.Primrec (fun t : ℕ =>
      myUpsample t.unpair.2.unpair.1 t.unpair.1 (myModPow2 t.unpair.2.unpair.2
        (2 ^ t.unpair.2.unpair.1))) :=
    (primrec.myUpsample.comp (hj.pair (hk.pair hmodj))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_isZero.comp (primrec_add₂ (primrec_sub₂ hups hmodk)
    (primrec_sub₂ hmodk hups))).of_eq fun t => rfl

end DomainTheory.NeighbourhoodSystems
