module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso
public import Mathlib.Order.Preorder.Chain

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

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

theorem le_chainUnion (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    {x : V.Element} (hx : x ∈ C) : x ≤ V.chainUnion C hne hchain :=
  fun _ hX => ⟨x, hx, hX⟩

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
end
