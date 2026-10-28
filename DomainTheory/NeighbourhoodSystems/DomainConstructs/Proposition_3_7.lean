module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem
variable {α β γ δ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}
open ApproximableMap
variable {V₃ : NeighborhoodSystem δ}

theorem substitution_toElementMap (F : ApproximableMap (prod V₀ V₁) V₂)
    (a : ApproximableMap V₃ V₀) (b : ApproximableMap V₃ V₁) (w : V₃.Element) :
    (F.comp (paired a b)).toElementMap w
      = (toMap₂ F).toElementMap₂ (a.toElementMap w) (b.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, toElementMap₂_toMap₂]
end

end DomainTheory.NeighbourhoodSystems
end
