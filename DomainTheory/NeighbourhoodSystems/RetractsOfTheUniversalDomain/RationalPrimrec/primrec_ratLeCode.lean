module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_qNumP
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_qNumN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_qDen

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem primrec_ratLeCode : Nat.Primrec ratLeCode := by
  have hc1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hc2 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hlhs : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.1 * qDen t.unpair.2 + qNumN t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumN.comp hc2) (primrec_qDen.comp hc1))
  have hrhs : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.2 * qDen t.unpair.1 + qNumN t.unpair.1 * qDen t.unpair.2) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc2) (primrec_qDen.comp hc1))
      (primrec_mul₂ (primrec_qNumN.comp hc1) (primrec_qDen.comp hc2))
  exact (primrec_isZero.comp (primrec_sub₂ hlhs hrhs)).of_eq fun t => by
    simp only [ratLeCode]

end DomainTheory.NeighbourhoodSystems
