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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QLookup
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_QLookup
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel_fuelTable_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

/-- **`QFuel r` is jointly primitive recursive in `(fuel, code)`.** Mirrors
`primrec_decodeFuelOkChar2` exactly. -/
theorem primrec_QFuel2 (hr : Nat.Primrec r) :
    Nat.Primrec (fun s : ℕ => QFuel r s.unpair.1 s.unpair.2) := by
  have hft := primrec_fuelTable (primrec_QLookup r hr)
  have hpack : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2 s.unpair.1) :=
    Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left
  have hcomp : Nat.Primrec (fun s => fuelTable (QLookup r) s.unpair.2 s.unpair.1) :=
    (hft.comp hpack).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnth : Nat.Primrec
      (fun s => nthCode (fuelTable (QLookup r) s.unpair.2 s.unpair.1) s.unpair.2 0) :=
    (primrec_nthCode.comp
      (hcomp.pair ((Nat.Primrec.right).pair (Nat.Primrec.const 0)))).of_eq
      fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact hnth.of_eq fun s => QFuel_fuelTable_eq r s.unpair.1 s.unpair.2 s.unpair.2 (le_refl _)

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
