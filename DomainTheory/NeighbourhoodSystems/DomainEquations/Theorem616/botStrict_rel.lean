/-ai
The strict map represented by the bottom element of the strict function space relates a set X to a set Y exactly when X is a neighbourhood and Y is the master neighbourhood.

Rewrite the relation through the strict representation, membership of bottom, and the master of the strict function space. If that membership holds, the constant-bottom strict map lies in the step neighbourhood, and the step and constant-map characterizations give the two conditions. If X is a neighbourhood and Y is the master, the step neighbourhood with master codomain contains the map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition67
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem616.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w


/-- The strict map represented by `⊥` of the strict function space relates `X` to `Y` exactly when
`X` is a neighbourhood and `Y` is the master output: it is the constant-`⊥` (least) strict map. -/
theorem botStrict_rel {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {X : Set α} {Y : Set β} :
    (toStrictMap (strictFun V₀ V₁).bot).1.rel X Y ↔ V₀.mem X ∧ Y = V₁.master := by
  rw [toStrictMap_rel, NeighborhoodSystem.mem_bot, strictFun_master]
  constructor
  · intro h
    have hcb : (⟨constMap V₀ V₁.bot, isStrict_constBot⟩ : StrictMap V₀ V₁) ∈ sstep X Y := by
      rw [h]; exact Set.mem_univ _
    rw [mem_sstep, constMap_rel, NeighborhoodSystem.mem_bot] at hcb
    exact hcb
  · rintro ⟨hX, rfl⟩
    exact sstep_cod_master hX

end DomainTheory.NeighbourhoodSystems
