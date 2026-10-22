module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.SplitSpec'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xyStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.if_swap_disjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.inter_diff_self_eq_empty

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`xyStep`'s two outputs, at two *different* sign bits, are pairwise disjoint** — the local,
one-step content behind `atomPair`'s eventual pairwise-disjointness invariant. -/
theorem xyStep_disjoint_of_ne {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xyStep split A B Xn b).1 ∩ (xyStep split A B Xn b').1 = ∅ ∧
      (xyStep split A B Xn b).2 ∩ (xyStep split A B Xn b').2 = ∅ :=
  ⟨if_swap_disjoint (inter_diff_self_eq_empty A Xn) hbb',
    if_swap_disjoint (hsplit hAB hBE Xn).2.2.2.2.2 hbb'⟩

end DomainTheory.NeighbourhoodSystems
