module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.primrec_ssysActiveChar

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem primrec_ssysConsistentBChar :
    Nat.Primrec (fun t => ssysConsistentBChar t.unpair.1 t.unpair.2) := by
  have hcond : Nat.Primrec
      (fun t => mulBit (ssysActiveChar t.unpair.1) (ssysActiveChar t.unpair.2)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair (primrec_ssysActiveChar.comp Nat.Primrec.left)
      (primrec_ssysActiveChar.comp Nat.Primrec.right))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hfuel : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2 + t.unpair.2.unpair.2 + 2) :=
    primrec_add₂ (primrec_add₂ (Nat.Primrec.right.comp Nat.Primrec.left)
      (Nat.Primrec.right.comp Nat.Primrec.right)) (Nat.Primrec.const 2)
  have hpack : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.1.unpair.2 + t.unpair.2.unpair.2 + 2)
      (Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1)) :=
    Nat.Primrec.pair hfuel (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.left)
      (Nat.Primrec.left.comp Nat.Primrec.right))
  have hcons : Nat.Primrec (fun t => consistentBChar
      (t.unpair.1.unpair.2 + t.unpair.2.unpair.2 + 2) t.unpair.1.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_consistentBChar2.comp hpack).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_selectFn hcond hcons (Nat.Primrec.const 1)).of_eq fun t => by
    simp only [ssysConsistentBChar]

end Exercise722

end DomainTheory.NeighbourhoodSystems
