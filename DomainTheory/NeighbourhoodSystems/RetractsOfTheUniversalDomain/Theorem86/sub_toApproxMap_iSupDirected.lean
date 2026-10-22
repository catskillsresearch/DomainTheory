module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_rel_iSupDirected

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`sub` commutes with directed unions of relations.** `sub`'s formula (`sub_rel`) is a positive
existential in `f`'s relation (`∃Y, ... ∧ f.rel Y Y ∧ ...`), so it commutes with an arbitrary union
of relations by pure logic (swapping the order of two existentials) — no directedness needed here
either, only for `iSupDirected` to be well-formed in the first place. -/
theorem sub_toApproxMap_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (sub (toApproxMap (iSupDirected φ hdir))).rel X Z ↔
      ∃ i, (sub (toApproxMap (φ i))).rel X Z := by
  simp only [sub_rel, toApproxMap_rel_iSupDirected]
  constructor
  · rintro ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩
    exact ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
  · rintro ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
    exact ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩

end Sub8_6

end DomainTheory.NeighbourhoodSystems
