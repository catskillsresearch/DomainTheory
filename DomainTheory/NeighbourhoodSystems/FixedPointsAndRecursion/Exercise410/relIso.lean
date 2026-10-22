module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.restrict
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_restrict
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.restrict_embed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.le_of_embed_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.10 (Scott 1981, PRG-19).** `|Dₐ| ≃o {x ∈ |𝒟| ∣ x ⊑ a}`: the relativized domain has
exactly the elements below `a` as its points, with the inherited order. -/
def relIso (a : V.Element) : (relSystem a).Element ≃o {x : V.Element // x ≤ a} where
  toFun g := ⟨embed a g, embed_le a g⟩
  invFun x := restrict a x.1 x.2
  left_inv g := restrict_embed a g
  right_inv x := Subtype.ext (embed_restrict a x.1 x.2)
  map_rel_iff' := by
    intro g₁ g₂
    constructor
    · intro h; exact le_of_embed_le a h
    · intro h; exact embed_mono a h

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
