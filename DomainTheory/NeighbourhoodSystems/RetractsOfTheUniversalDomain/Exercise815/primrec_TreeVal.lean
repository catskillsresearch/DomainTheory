/-ai
If the basic-neighbourhood enumeration is primitive recursive, then evaluation of a term-algebra code is primitive recursive.

Fuel-bounded evaluation of a packed pair is primitive recursive, and packing one more than the code with the code itself is primitive recursive. Fuel-bounded evaluation at fuel one more than the code is evaluation of the code.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_QFuel2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

theorem primrec_TreeVal (hr : Nat.Primrec r) : Nat.Primrec (TreeVal r) := by
  have h2 := primrec_QFuel2 r hr
  have hpack : Nat.Primrec (fun c : ℕ => Nat.pair (c + 1) c) :=
    (primrec_add₂ Nat.Primrec.id (Nat.Primrec.const 1)).pair Nat.Primrec.id
  refine (h2.comp hpack).of_eq fun c => ?_
  show QFuel r (Nat.pair (c + 1) c).unpair.1 (Nat.pair (c + 1) c).unpair.2 = TreeVal r c
  rw [unpair_pair_fst, unpair_pair_snd]
  rfl

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
