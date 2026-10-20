module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.monoFix_le_preFix
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.monoFix_preFix

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem





/-- **Exercise 4.13(1) (Scott 1981, PRG-19).** `monoFix f ha` is a fixed point: `f(b) = b`. (After
`f(b) ⊑ b`, monotonicity gives `f(f(b)) ⊑ f(b)`, so `f(b)` is itself a pre-fixed point, whence
`b ⊑ f(b)`.) -/
theorem monoFix_isFixed (f : V.Element → V.Element) (hf : Monotone f) {a : V.Element}
    (ha : f a ≤ a) : f (monoFix f ha) = monoFix f ha := by
  have hfb : f (monoFix f ha) ≤ monoFix f ha := monoFix_preFix f hf ha
  have hbf : monoFix f ha ≤ f (monoFix f ha) :=
    monoFix_le_preFix f ha (hf hfb)
  exact le_antisymm hfb hbf

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
