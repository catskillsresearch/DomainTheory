/-ai
The singleton map relates the enumerated neighbourhood of n to the neighbourhood coded by k if and only if some index in the decoded list of k lies above the neighbourhood of n.

Rewrite the relation as singleton membership in the power domain. From a witness neighbourhood Y, the enumerated neighbourhood of n lies in the down-set of Y by the principal inclusion, hence lies in the coded neighbourhood by the down-set inclusion, and membership supplies an index whose enumerated neighbourhood contains it. Conversely, the enumerated neighbourhood of that index, the fact that the coded neighbourhood is a power-domain neighbourhood, and the inclusion of its down-set in the coded neighbourhood given by the down-set criterion at the index itself, form the witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


variable (P : ComputablePresentation V)

/-- **Proposition 7.12 — code form of singleton membership.** `{↑X_n}` relates to `Y_k` iff some
index in `dl k` lies above `X_n`. -/
theorem PDsingletonApproxMap_rel_Ypd_iff {n k : ℕ} :
    ((PDsingletonApproxMap (V := V))).rel (P.X n) (V.Ypd P k) ↔
      ∃ b ∈ decodeList k, P.X n ⊆ P.X b := by
  rw [PDsingletonApproxMap_rel (hX := P.mem_X n), PDmem_singleton, PowerDomain_mem]
  constructor
  · rintro ⟨Y, hYpr, _, hsub⟩
    have hn : P.X n ∈ V.upSet Y := ⟨P.mem_X n, hYpr.2⟩
    obtain ⟨b, hb, hPab⟩ := (V.mem_Ypd P).mp (hsub hn)
    exact ⟨b, hb, hPab.2⟩
  · intro ⟨b, hb, hnb⟩
    refine ⟨P.X b, ⟨P.mem_X b, hnb⟩, V.Ypd_isPDmem P k,
      (V.upSet_subset_Ypd_iff P).mpr ⟨b, hb, subset_rfl⟩⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
