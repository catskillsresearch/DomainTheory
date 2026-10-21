/-ai
The binary join map from the product of an effectively given domain to its power domain is computable: its neighbourhood relation is two independent singleton tests.

Computability of the singleton map makes its relation on enumerated neighbourhoods recursively enumerable. Pairing the first half of the first component of a code with the second component, and pairing the second half of the first component with the second component, are primitive recursive. The relation of the product presentation against the power-domain presentation unpacks to a product neighbourhood together with the two singleton relations, and the two singleton relations reassemble with the product of the two enumerated neighbourhoods. That predicate is the conjunction of the singleton predicate composed with the two pairings.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.singleton_isComputable

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


variable (P : ComputablePresentation V)

/-- **Proposition 7.12 — the binary join map is computable.** Two independent singleton tests. -/
theorem PDfinJoinApproxMap₂_isComputable (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    IsComputableMap (prodPresentation P P)
      (V.PDPresentation P cons hconsp hcons) (finJoinMap_prod (V := V)) := by
  have hs : REPred (fun s => (PDsingletonApproxMap (V := V)).rel (P.X s.unpair.1) (V.Ypd P s.unpair.2)) :=
    singleton_isComputable (V := V) P cons hconsp hcons
  have hra : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  have hrb : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine REPred.of_iff (fun t => by
    dsimp [prodPresentation_X, finJoinMap_prod, ofMap₂]
    simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd,
      PDPresentation, unpair_pair_fst, unpair_pair_snd]
    constructor
    · rintro ⟨_, ⟨h1, h2⟩⟩
      exact ⟨h1, h2⟩
    · intro ⟨h1, h2⟩
      refine ⟨prod_mem_prodNbhd (P.mem_X _) (P.mem_X _), h1, h2⟩) ((hs.comp hra).and (hs.comp hrb))

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
