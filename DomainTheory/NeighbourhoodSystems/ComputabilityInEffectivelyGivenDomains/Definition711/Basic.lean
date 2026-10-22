module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDmemFinJoin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoinZero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoinSucc
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDsingleton
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDmem_finJoinZero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


theorem PDmem_finJoinSucc {m : ℕ} (xs : Fin (m + 1) → V.Element) {W : Set (Set α)} :
    (V.PDfinJoinSucc xs).mem W ↔ V.PDmemFinJoin xs W := Iff.rfl


@[simp] theorem PDmem_singleton {x : V.Element} {W : Set (Set α)} :
    (V.PDsingleton x).mem W ↔
      ∃ X, x.mem X ∧ V.PowerDomain.mem W ∧ V.upSet X ⊆ W := by
  rw [PDsingleton, PDfinJoin, PDmem_finJoinSucc, PDmemFinJoin]
  constructor
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨X 0, hX 0, hPD, hsub 0⟩
  · rintro ⟨X, hX, hPD, hsub⟩
    refine ⟨fun _ => X, fun _ => hX, hPD, fun _ => hsub⟩
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
