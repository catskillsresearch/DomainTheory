/-ai
A fixed point of a closure operator is compact if and only if it equals the image of the principal element of a single neighbourhood.

If it is compact, compactness applied to the generating family, whose directed supremum is the fixed point, yields one neighbourhood whose image lies above the fixed point. The principal element of that neighbourhood lies below the fixed point, so monotonicity of the element map and the fixed-point equation give the reverse inequality. Conversely, the image of the principal element of any neighbourhood is compact among fixed points.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)






























/-- **Exercise 8.14, the final question, answered exactly.** `y ∈ Fix(a)` is compact (i.e. is a
*finite element* of the fixed-point domain) **iff** `y = a(↑X)` for a single `E`-neighbourhood `X`.
The forward direction is a sandwich argument: `y` is the directed union of the compacts `a(↑X)`
(`X ∈ y`, `toElementMap_eq_iSupDirected_genFamily`), so compactness pulls out a single witness `X`
with `y ⊑ a(↑X)`; the reverse inequality `a(↑X) ⊑ y` is automatic since `X ∈ y`. -/
theorem isCompactFix_iff (y : FixSet a) :
    IsCompactFix h y ↔ ∃ (X : Set α) (hX : E.mem X), y.1 = a.toElementMap (E.principal hX) := by
  constructor
  · intro hc
    obtain ⟨i, hi⟩ := hc (genFamily h y) (genFamily_directed h y)
      (le_of_eq (toElementMap_eq_iSupDirected_genFamily h y))
    have hX : E.mem i.1 := y.1.sub i.2
    refine ⟨i.1, hX, le_antisymm hi ?_⟩
    have h1 : E.principal hX ≤ y.1 := principal_le_of_mem i.2
    have h2 := a.toElementMap_mono h1
    rwa [y.2] at h2
  · rintro ⟨X, hX, hy⟩
    exact hy ▸ isCompactFix_toElementMap_principal h hX

end FiniteDomain
end DomainTheory.NeighbourhoodSystems
