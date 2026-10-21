/-ai
If a doubly indexed set is a neighbourhood of the double iteration, then its reindexing is a neighbourhood of the iteration.

Each fiber of the reindexing is a double fiber, hence a neighbourhood of the system. For the cofinite master condition, take the outer cofinite bound of the doubly indexed neighbourhood and an inner bound that makes every double fiber below that outer bound equal the master. If an index is at least the pairing of those two bounds, then either its first unpaired component meets the outer bound, so the fiber is the master of the iteration, or its second component meets the inner bound. Both components cannot lie strictly below the two bounds, because the pairing would then be strictly smaller.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2_of_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.exists_inner_bound
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.pair_lt_pair_of_lt

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashMap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2080_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2081_isComputable
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

theorem reindexG_mem {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) :
    (iterSys V).mem (reindexG S) := by
  obtain ⟨No, hNo⟩ := hS.2
  obtain ⟨M, hM⟩ := exists_inner_bound hS No
  refine ⟨fun k => ?_, Nat.pair No M, fun k hk => ?_⟩
  · -- fibers are `V`-neighbourhoods
    rw [fiber_reindexG]; exact mem_fiber2_of_mem hS _ _
  · -- cofinite-`Δ`
    rw [fiber_reindexG]
    set i := (Nat.unpair k).1 with hi
    set j := (Nat.unpair k).2 with hj
    by_cases hiN : i < No
    · by_cases hjM : j < M
      · exfalso
        have hklt : Nat.pair i j < Nat.pair No M := pair_lt_pair_of_lt hiN hjM
        rw [pair_unpair] at hklt
        omega
      · exact hM i hiN j (not_lt.mp hjM)
    · have h1 : fiber S i = (iterSys V).master := hNo i (not_lt.mp hiN)
      show fiber2 S i j = V.master
      rw [fiber2, h1, fiber_iterSys_master]

end Exercise718

end DomainTheory.NeighbourhoodSystems
