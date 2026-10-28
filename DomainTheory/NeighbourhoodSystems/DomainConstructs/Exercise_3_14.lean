module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_2
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
variable {α : Type*} (V : NeighborhoodSystem α)

def diag : ApproximableMap V (prod V V) := paired (idMap V) (idMap V)

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem diag_rel {Z : Set α} {P : Set (α ⊕ α)} :
    (diag V).rel Z P ↔
      (prod V V).mem P ∧ (idMap V).rel Z (Sum.inl ⁻¹' P) ∧ (idMap V).rel Z (Sum.inr ⁻¹' P) :=
  Iff.rfl

@[simp] theorem toElementMap_diag (x : V.Element) :
    (diag V).toElementMap x = pair x x := by
  rw [diag, toElementMap_paired, toElementMap_idMap]

theorem proj₀_comp_diag : (proj₀ V V).comp (diag V) = idMap V :=
  proj₀_comp_paired (idMap V) (idMap V)
end

section
set_option linter.unusedVariables false

theorem example_314.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α α) α V
      (@DomainTheory.NeighbourhoodSystems.prod α α V V) V (@DomainTheory.NeighbourhoodSystems.proj₀ α α V V)
      (@DomainTheory.NeighbourhoodSystems.diag α V))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V) :=
  @DomainTheory.NeighbourhoodSystems.proj₀_comp_diag
end

section
open NeighborhoodSystem ApproximableMap
variable {α : Type*} (V : NeighborhoodSystem α)

theorem proj₁_comp_diag : (proj₁ V V).comp (diag V) = idMap V :=
  proj₁_comp_paired (idMap V) (idMap V)
end
end DomainTheory.NeighbourhoodSystems
end
