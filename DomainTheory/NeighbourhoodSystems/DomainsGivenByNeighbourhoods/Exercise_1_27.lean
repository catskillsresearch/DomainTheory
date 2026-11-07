module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem_more

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's Exercise 1.27: boundedness is finitary; pairwise consistency matches bounded
    principal pairs; sSup is the least upper bound of a bounded set. -/
theorem exercise_1_27 :
    (∀ (X : Set V.Element), V.Bounded X ↔ ∀ S ⊆ X, S.Finite → V.Bounded S) ∧
      (∀ {U W : Set α} (hU : V.mem U) (hW : V.mem W),
        V.Consistent (pairSeq U W) 2 ↔ V.Bounded {V.principal hU, V.principal hW}) ∧
      (∀ (X : Set V.Element) (hX : V.Bounded X) {x : V.Element}, x ∈ X → x ≤ V.sSup X hX) ∧
      (∀ (X : Set V.Element) (hX : V.Bounded X) {z : V.Element},
        (∀ x ∈ X, x ≤ z) → V.sSup X hX ≤ z) :=
  ⟨V.bounded_iff_finite_bounded, V.consistent_pair_iff_bounded,
    fun X hX _x hx => V.le_sSup X hX hx, fun X hX _z hz => V.sSup_le X hX hz⟩

