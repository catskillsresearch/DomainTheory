module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_qNumP
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_qNumN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_qDen

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

























theorem primrec_ratMidCode : Nat.Primrec ratMidCode := by
  have hc1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hc2 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hnumP : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.1 * qDen t.unpair.2 + qNumP t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumP.comp hc2) (primrec_qDen.comp hc1))
  have hnumN : Nat.Primrec (fun t : ℕ =>
      qNumN t.unpair.1 * qDen t.unpair.2 + qNumN t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumN.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumN.comp hc2) (primrec_qDen.comp hc1))
  have hden : Nat.Primrec (fun t : ℕ => 2 * qDen t.unpair.1 * qDen t.unpair.2 - 1) :=
    primrec_sub₂
      (primrec_mul₂ (primrec_mul₂ (Nat.Primrec.const 2) (primrec_qDen.comp hc1))
        (primrec_qDen.comp hc2))
      (Nat.Primrec.const 1)
  exact (Nat.Primrec.pair (Nat.Primrec.pair hnumP hnumN) hden).of_eq fun t => by
    simp only [ratMidCode]

end DomainTheory.NeighbourhoodSystems
