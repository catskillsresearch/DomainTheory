/-ai
If the point filters of two reals agree, then the reals are equal.

Suppose they differ, and take the case where the first is strictly smaller. Density gives a rational strictly between them and a rational strictly above the larger real. The open interval between those rationals is a rational-interval neighbourhood containing the larger real, so it belongs to the larger point filter and hence to the smaller one. Membership would require the smaller real to lie strictly above the intermediate rational, contradicting the choice of that rational. The symmetric case, with the second real strictly smaller, is the same construction with the two reals exchanged.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem


/-- **Exercise 1.17 — `ℝ ↪ |𝒟|`.** Distinct reals give distinct point filters: between any two
reals lies a rational interval separating them. -/
theorem filterAt_injective {s t : ℝ} (h : filterAt s = filterAt t) : s = t := by
  by_contra hst
  rcases lt_or_gt_of_ne hst with hlt | hlt
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb⟩ := exists_rat_gt t
    have hint : ratIntervalMem (Set.Ioo (a : ℝ) (b : ℝ)) :=
      Or.inr ⟨a, b, by exact_mod_cast ha2.trans hb, rfl⟩
    have htmem : (filterAt t).mem (Set.Ioo (a : ℝ) (b : ℝ)) := ⟨hint, ha2, hb⟩
    rw [← h] at htmem
    exact absurd htmem.2.1 (not_lt.mpr ha1.le)
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb⟩ := exists_rat_gt s
    have hint : ratIntervalMem (Set.Ioo (a : ℝ) (b : ℝ)) :=
      Or.inr ⟨a, b, by exact_mod_cast ha2.trans hb, rfl⟩
    have hsmem : (filterAt s).mem (Set.Ioo (a : ℝ) (b : ℝ)) := ⟨hint, ha2, hb⟩
    rw [h] at hsmem
    exact absurd hsmem.2.1 (not_lt.mpr ha1.le)

end RatInterval
end DomainTheory.NeighbourhoodSystems
