module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise124
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415.exists_maximal_fixedPoint

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.monoFix_least
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- **Exercise 4.15 (Scott 1981, PRG-19).** A monotone `f : |𝒟| → |𝒟|` has a *least* fixed point.
(Having a maximal fixed point `m` gives a pre-fixed point `f(m) ⊑ m`; Exercise 4.13(1)'s `monoFix`
then constructs the least fixed point `⋂{x ∣ f(x) ⊑ x}`.) -/
theorem exists_least_fixedPoint (f : V.Element → V.Element) (hf : Monotone f) :
    ∃ b, f b = b ∧ ∀ y, f y = y → b ≤ y := by
  obtain ⟨m, hfm, _⟩ := exists_maximal_fixedPoint f hf
  exact ⟨monoFix f (le_of_eq hfm), monoFix_isFixed f hf (le_of_eq hfm),
    fun y hy => monoFix_least f (le_of_eq hfm) hy⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
