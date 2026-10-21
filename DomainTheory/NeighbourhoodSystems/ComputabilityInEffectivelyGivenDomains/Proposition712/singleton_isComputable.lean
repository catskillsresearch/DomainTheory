/-ai
When a domain is effectively given, the singleton map is a computable map from its presentation to the induced presentation of the power domain.

The inclusion decider, swapped, closed under bounded existence over a decoded list, and swapped again, decides the stated bounded existence of a larger index. That relation is the computability relation: the power-domain presentation enumerates the coded neighbourhoods, and the singleton relation with a coded neighbourhood is this bounded existence.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap_rel_Ypd_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


variable (P : ComputablePresentation V)

/-- **Proposition 7.12 — `λ x. {x}` is computable when `D` is effectively given.** -/
theorem singleton_isComputable (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    IsComputableMap P (V.PDPresentation P cons hconsp hcons) ((PDsingletonApproxMap (V := V))) := by
  have h := P.incl_computable.swap.bExistsList.swap
  refine (RecDecidable.of_iff (fun s => ?_) h).re
  show PDsingletonApproxMap (V := V).rel (P.X s.unpair.1) ((V.PDPresentation P cons hconsp hcons).X s.unpair.2) ↔
      ∃ e ∈ decodeList s.unpair.2, P.X s.unpair.1 ⊆ P.X e
  simp only [PDPresentation]
  apply PDsingletonApproxMap_rel_Ypd_iff (V := V)

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
