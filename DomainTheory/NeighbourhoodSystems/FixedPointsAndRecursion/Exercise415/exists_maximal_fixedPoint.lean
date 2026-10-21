/-ai
A monotone endomap of the elements of a domain has a maximal fixed point: a fixed point that agrees with every larger fixed point.

Zorn's lemma is applied to the set of post-fixed points. The empty chain is bounded by the bottom element, which is post-fixed because bottom lies below its image. A nonempty chain is bounded by its union, which lies above each member and is post-fixed: a neighbourhood of the union belongs to some member, that member lies below the union and hence below the image of the union, and the member is post-fixed, so the neighbourhood belongs to the image of the union. A maximal post-fixed point lies below its image. Monotonicity makes the image post-fixed, and maximality places the image below the point, so the two are equal. A fixed point above this point is post-fixed, and maximality places it below the point.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise124
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- **Exercise 4.15 (Scott 1981, PRG-19).** A monotone `f : |𝒟| → |𝒟|` has a *maximal* fixed point:
some `m` with `f(m) = m` that admits no strictly larger fixed point. -/
theorem exists_maximal_fixedPoint (f : V.Element → V.Element) (hf : Monotone f) :
    ∃ m, f m = m ∧ ∀ y, f y = y → m ≤ y → y ≤ m := by
  -- Zorn on the set of post-fixed points.
  set S : Set V.Element := {x | x ≤ f x} with hS
  have ih : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ?_, fun z hz => ((Set.mem_empty_iff_false z).mp hz).elim⟩
      show (⊥ : V.Element) ≤ f ⊥
      exact _root_.bot_le
    · refine ⟨V.chainUnion c hne hchain, ?_, fun z hz => V.le_chainUnion c hne hchain hz⟩
      -- `⊔c` is post-fixed: each `x ∈ c` has `x ⊑ f x ⊑ f(⊔c)`.
      show V.chainUnion c hne hchain ≤ f (V.chainUnion c hne hchain)
      intro Z hZ
      obtain ⟨x, hxc, hxZ⟩ := hZ
      have hxle : x ≤ V.chainUnion c hne hchain := V.le_chainUnion c hne hchain hxc
      exact (le_trans (hcS hxc) (hf hxle)) Z hxZ
  obtain ⟨m, hm⟩ := zorn_le₀ S ih
  have hms : m ≤ f m := hm.1
  have hfm_le_m : f m ≤ m := hm.2 (hf hms) hms
  refine ⟨m, le_antisymm hfm_le_m hms, fun y hy hmy => hm.2 ?_ hmy⟩
  exact le_of_eq hy.symm

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
