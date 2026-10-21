/-ai
The activity characteristic of a coded index is primitive recursive.

The map pairing one more than the second unpaired component with the first unpaired component is primitive recursive. Composing the primitive-recursive fuel-bounded decode characteristic and the primitive-recursive nonemptiness characteristic with that packing gives the two factors, and their bit product is the activity characteristic.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem primrec_ssysActiveChar : Nat.Primrec ssysActiveChar := by
  have hpack : Nat.Primrec (fun n : ℕ => Nat.pair (n.unpair.2 + 1) n.unpair.1) :=
    Nat.Primrec.pair (primrec_add₂ Nat.Primrec.right (Nat.Primrec.const 1)) Nat.Primrec.left
  have h1 : Nat.Primrec (fun n => decodeFuelOkChar (n.unpair.2 + 1) n.unpair.1) :=
    (primrec_decodeFuelOkChar2.comp hpack).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h2 : Nat.Primrec (fun n => decideNonemptyBChar (n.unpair.2 + 1) n.unpair.1) :=
    (primrec_decideNonemptyBChar2.comp hpack).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_mulBit.comp (Nat.Primrec.pair h1 h2)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd, ssysActiveChar]

end Exercise722

end DomainTheory.NeighbourhoodSystems
