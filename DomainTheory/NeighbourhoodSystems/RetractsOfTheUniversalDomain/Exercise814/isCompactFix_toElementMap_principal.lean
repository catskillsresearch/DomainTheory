/-ai
For any neighbourhood, the image of its principal element under a closure operator is compact among fixed points.

If that image lies below a directed supremum of fixed points, inflation puts the principal element itself below the same supremum. Compactness of the principal element yields an index at which the family lies above it. Monotonicity of the element map and the fixed-point equation for that family value place the image below it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.le_toElementMap_of_isClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsCompactFix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section ClosureOperator

variable {a : ApproximableMap E E}

/-- **The key new fact.** `a(↑X)`, for any `E`-neighbourhood `X`, is compact w.r.t. directed unions
*within `Fix(a)`* — even though it need not be principal in `E` itself. Proof: if
`a(↑X) ⊑ ⋃ᵢ d(i)` then (since `↑X ⊑ a(↑X)` by inflation) `↑X ⊑ ⋃ᵢ d(i)`, so by compactness of `↑X`
in `E` (`principal_isCompactElt`), `↑X ⊑ d(i)` for some `i`; applying `a` (monotone) and using that
`d(i)` is already fixed gives `a(↑X) ⊑ d(i)`. -/
theorem isCompactFix_toElementMap_principal (h : ClosureOperator a) {X : Set α} (hX : E.mem X) :
    IsCompactFix h ⟨a.toElementMap (E.principal hX), toElementMap_idem h.out.1 _⟩ := by
  intro I _ d hdir hle
  have hle' : E.principal hX ≤ iSupDirected (fun i => (d i).1) hdir :=
    (le_toElementMap_of_isClosureOperator h (E.principal hX)).trans hle
  obtain ⟨i, hi⟩ := principal_isCompactElt hX (fun i => (d i).1) hdir hle'
  refine ⟨i, ?_⟩
  have h2 := a.toElementMap_mono hi
  rwa [(d i).2] at h2

end ClosureOperator

end DomainTheory.NeighbourhoodSystems
