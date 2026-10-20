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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nodeCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

theorem primrec_Q2inter : Nat.Primrec (fun t : ℕ => Q2inter t.unpair.1 t.unpair.2) := by
  have heq : (fun t : ℕ => Q2inter t.unpair.1 t.unpair.2) = fun t => Nat.pair 1 t := by
    funext t; unfold Q2inter nodeCode; rw [pair_unpair]
  rw [heq]
  exact Nat.Primrec.pair (Nat.Primrec.const 1) Nat.Primrec.id

end TreeVal2

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
