module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.commute_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.iterElem_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.iterElem_zerou27

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 5.9 (Scott 1981, PRG-19).** If `f, g` commute and `f(⊥) = g(⊥)`, then
`fix(f) = fix(g)`. -/
theorem fixElement_eq_of_commuting_bot {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f)
    (hbot : f.toElementMap V.bot = g.toElementMap V.bot) :
    f.fixElement = g.fixElement := by
  -- `g(fⁿ⊥) = fⁿ⁺¹⊥`.
  have hshift : ∀ n, g.toElementMap (f.iterElem n) = f.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', iterElem_succ, iterElem_zero', ← hbot]
    | succ k ih =>
      rw [iterElem_succ, ← commute_apply hcomm, ih]
      exact (iterElem_succ f (k + 1)).symm
  -- `g(fix f) = fix f`.
  have hgfixf : g.toElementMap f.fixElement = f.fixElement := by
    rw [fixElement_eq_iSupDirected f, toElementMap_iSupDirected]
    apply le_antisymm
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hshift n]
      exact NeighborhoodSystem.le_iSupDirected f.iterElem _ (n + 1)
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      calc f.iterElem n ≤ f.iterElem (n + 1) := iterElem_mono f (Nat.le_succ n)
        _ = g.toElementMap (f.iterElem n) := (hshift n).symm
        _ ≤ _ := NeighborhoodSystem.le_iSupDirected (fun m => g.toElementMap (f.iterElem m)) _ n
  -- symmetric: `f(fix g) = fix g`.
  have hshift' : ∀ n, f.toElementMap (g.iterElem n) = g.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', iterElem_succ, iterElem_zero', hbot]
    | succ k ih =>
      rw [iterElem_succ, commute_apply hcomm, ih]
      exact (iterElem_succ g (k + 1)).symm
  have hffixg : f.toElementMap g.fixElement = g.fixElement := by
    rw [fixElement_eq_iSupDirected g, toElementMap_iSupDirected]
    apply le_antisymm
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hshift' n]
      exact NeighborhoodSystem.le_iSupDirected g.iterElem _ (n + 1)
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      calc g.iterElem n ≤ g.iterElem (n + 1) := iterElem_mono g (Nat.le_succ n)
        _ = f.toElementMap (g.iterElem n) := (hshift' n).symm
        _ ≤ _ := NeighborhoodSystem.le_iSupDirected (fun m => f.toElementMap (g.iterElem m)) _ n
  apply le_antisymm
  · exact fixElement_le_of_toElementMap_le f (le_of_eq hffixg)
  · exact fixElement_le_of_toElementMap_le g (le_of_eq hgfixf)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
