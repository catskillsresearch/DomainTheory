module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.partrecLam

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.NatDom (N natElem)
open DomainTheory.NeighbourhoodSystems.PartrecLam

/-- Scott's Theorem 5.6: every unary partial recursive function is realized by a
strict approximable endomap on the number domain. -/
theorem theorem_56 {h : ℕ →. ℕ}
    (H : Nat.Partrec' (fun v : List.Vector ℕ 1 => h v.head)) :
    ∃ τ : ApproximableMap N N,
      (∀ a m, m ∈ h a → τ.toElementMap (natElem a) = natElem m) ∧
      (∀ a, ¬ (h a).Dom → τ.toElementMap (natElem a) = N.bot) ∧
      τ.toElementMap N.bot = N.bot :=
  partrec_one H

end DomainTheory.NeighbourhoodSystems
