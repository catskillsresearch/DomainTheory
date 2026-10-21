/-ai
For every code up to a given bound, the entry of the fuel table built from the lookup step equals the fuel-indexed evaluator.

This is the general agreement of a fuel table with a recursion. The lookup step matches the fuel body after the packed input is unpacked, and the body depends on the previous function only at the two children, each of which is at most the code.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody_local
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QLookup
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

theorem QFuel_fuelTable_eq :
    ∀ fuel bound c, c ≤ bound →
      nthCode (fuelTable (QLookup r) bound fuel) c 0 = QFuel r fuel c :=
  fuelTable_eq_of_recursion (F := QFuel r) (Body := QBody r) (fun _ => rfl) (fun _ _ => rfl)
    (fun table c => by unfold QLookup QBody; simp only [unpair_pair_fst, unpair_pair_snd])
    (fun f g c h => QBody_local r f g c
      (h c.unpair.2.unpair.1 (le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)))
      (h c.unpair.2.unpair.2 (le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c))))

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
