/-ai
If Y belongs to E, X belongs to an element x, X is contained in Y, and an approximable endomap a relates X to itself, then Y belongs to a of x.

The domain of the self-relation is a neighbourhood, so that neighbourhood belongs to a of its principal. The principal lies below x, monotonicity of the element map puts the neighbourhood in a of x, and upward closure along the inclusion puts Y there.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}





/-- **The "easy" (`⟸`) half of formula (ii), isolated.** Valid for **any** approximable map
`a : E → E` with **no hypothesis on `a` at all** — not even that `a` satisfies the rest of formula
(ii), let alone that it is a finitary projection. Pure monotonicity + up-closure: `↑X ≤ x`
(`principal_le_of_mem`) pushes `a`'s self-relation at `X` up to `x` (`toElementMap_mono`), and
`X ⊆ Y` finishes by up-closure. Isolated from `isFinitaryProjection_of_formula`'s own proof (where
it was the `←` branch of the `constructor`) because Exercise 8.27(b)(3) needs exactly this half,
unconditionally, for `a := piD d` — independently of whether the *rest* of formula (ii) holds. -/
theorem mem_of_exists_rel_self {a : ApproximableMap E E} (x : E.Element) {Y : Set α}
    (hYE : E.mem Y) {X : Set α} (hXx : x.mem X) (hXY : X ⊆ Y) (hXaX : a.rel X X) :
    (a.toElementMap x).mem Y := by
  have hX : E.mem X := a.rel_dom hXaX
  have hmem : (a.toElementMap (E.principal hX)).mem X := (a.rel_iff_mem_principal hX).mp hXaX
  have hle : E.principal hX ≤ x := principal_le_of_mem hXx
  have hXmem : (a.toElementMap x).mem X := (a.toElementMap_mono hle) X hmem
  exact (a.toElementMap x).up_mem hXmem hYE hXY

end DomainTheory.NeighbourhoodSystems
