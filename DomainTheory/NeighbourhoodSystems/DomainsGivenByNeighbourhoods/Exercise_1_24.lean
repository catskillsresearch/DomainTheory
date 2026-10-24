module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_22

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L532 EXERCISE 1.24 extending partial elements -/
/-- **Exercise 1.24 — the union of a chain of filters is a filter.** For a non-empty chain `C` of
filters, `⋃ C = {X ∣ ∃ x ∈ C, X ∈ x}` is again a filter. The intersection axiom uses chain
totality: given `X ∈ x` and `Y ∈ y` with `x, y ∈ C`, one of `x ⊑ y`, `y ⊑ x` holds, and the larger
filter contains both `X` and `Y`, hence `X ∩ Y`. -/
def chainUnion (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C) : V.Element where
  mem X := ∃ x ∈ C, x.mem X
  sub := by rintro X ⟨x, _, hxX⟩; exact x.sub hxX
  master_mem := by obtain ⟨x, hxC⟩ := hne; exact ⟨x, hxC, x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨x, hxC, hxX⟩ ⟨y, hyC, hyY⟩
    rcases hchain.total hxC hyC with hxy | hyx
    · exact ⟨y, hyC, y.inter_mem (hxy X hxX) hyY⟩
    · exact ⟨x, hxC, x.inter_mem hxX (hyx Y hyY)⟩
  up_mem := by
    rintro X Y ⟨x, hxC, hxX⟩ hY hXY
    exact ⟨x, hxC, x.up_mem hxX hY hXY⟩

/-- Every member of the chain approximates the union `⋃ C`. -/
theorem le_chainUnion (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    {x : V.Element} (hx : x ∈ C) : x ≤ V.chainUnion C hne hchain :=
  fun _ hX => ⟨x, hx, hX⟩

/-- **Exercise 1.24 — partial elements extend to total ones (AC).** Using Zorn's lemma, every
element `x` admits a *total* element `t` with `x ⊑ t`. The upper bound of any non-empty chain in
`Ici x` is its `chainUnion`, so a maximal element exists; maximality is exactly totality
(`IsMax = IsTotal`). -/
theorem exists_total_ge (x : V.Element) : ∃ t, V.IsTotal t ∧ x ≤ t := by
  obtain ⟨m, hxm, hmax⟩ :=
    zorn_le_nonempty_Ici₀ x
      (fun c _ hchain y hy =>
        ⟨V.chainUnion c ⟨y, hy⟩ hchain, fun z hz => V.le_chainUnion c ⟨y, hy⟩ hchain hz⟩)
      x le_rfl
  exact ⟨m, fun y hy => hmax hy, hxm⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section

set_option linter.unusedVariables false

theorem example_124.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
  ∃ (t : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal α V t)
      (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x t) :=
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_total_ge
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
namespace DomainTheory.NeighbourhoodSystems
namespace FinalSegment
section

open NeighborhoodSystem

/-- In a linear order, any two upper sets are nested. (Hence final segments are
*nested-or-disjoint* — in fact always nested.) -/
theorem upperSet_subset_or {Δ : Type*} [LinearOrder Δ] {X Y : Set Δ}
    (hX : IsUpperSet X) (hY : IsUpperSet Y) : X ⊆ Y ∨ Y ⊆ X := by
  by_cases h : X ⊆ Y
  · exact Or.inl h
  · right
    rw [Set.not_subset] at h
    obtain ⟨a, haX, haY⟩ := h
    intro b hbY
    rcases le_total a b with hab | hba
    · exact hX hab haX
    · exact absurd (hY hba hbY) haY
end

end FinalSegment
end DomainTheory.NeighbourhoodSystems
end
