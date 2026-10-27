module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

structure IsComputableSplit {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
    (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (split : Set α → Set γ → Set α → Set γ × Set γ) where

  posIdx : ℕ → ℕ → ℕ → ℕ

  negIdx : ℕ → ℕ → ℕ → ℕ

  posIdx_primrec : Nat.Primrec (fun t => posIdx t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)

  negIdx_primrec : Nat.Primrec (fun t => negIdx t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)

  posIdx_spec : ∀ n m k, (split (P.X n) (Q.X m) (P.X k)).1 ≠ ∅ →
    (split (P.X n) (Q.X m) (P.X k)).1 = Q.X (posIdx n m k)

  negIdx_spec : ∀ n m k, (split (P.X n) (Q.X m) (P.X k)).2 ≠ ∅ →
    (split (P.X n) (Q.X m) (P.X k)).2 = Q.X (negIdx n m k)


end DomainTheory.NeighbourhoodSystems
