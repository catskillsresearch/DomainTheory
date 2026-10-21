/-ai
Upsampling a mask from one level to a higher level is primitive recursive on a triple code. It iterates the joint upsampling step for the difference of the levels and then truncates the resulting mask to two to the power of the target level.

The joint step, read from the inner right component, is primitive recursive, and so is primitive recursion from the identity with that step. Pairing the outer component with the inner mask, subtracting the outer level from the middle level, and raising two to the middle level are primitive recursive. Composing the primitive-recursive truncation with the pairing of the iterated right component and that power is primitive recursive. Simplifying the pairing identities, unfolding the upsample, and rewriting primitive recursion on a constant step as iteration identifies this composition with the upsample.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myUpsampleJointStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myUpsample :
    Nat.Primrec (fun t => myUpsample t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hstep : Nat.Primrec (fun w => myUpsampleJointStep w.unpair.2.unpair.2) :=
    primrec_myUpsampleJointStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec primrec_id hstep
  have hz : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) :=
    Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1 - t.unpair.1) :=
    primrec_sub₂ (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hmodpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.2.unpair.1) :=
    primrec_two_pow (Nat.Primrec.left.comp Nat.Primrec.right)
  refine (primrec_myModPow2.comp ((Nat.Primrec.right.comp (hprec.comp (hz.pair hn))).pair
    hmodpow)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  unfold myUpsample
  rw [rec_const_iterate]

end DomainTheory.NeighbourhoodSystems
