/-ai
The order isomorphism of Proposition 8.2 identifies an element of the subsystem with its image under the injection, which is a fixed point of the subsystem retraction, and identifies a fixed point with its image under the projection. The left inverse rewrites the projection of an injected element as the composite of the projection after the injection, which is the identity, so the element map of the identity returns the element. The right inverse uses that a fixed point equals the composite of the injection after the projection applied to it, which is the injection of its projection. If the injected images are ordered, monotonicity of the projection and the same identity recover the order of the elements; if the elements are ordered, monotonicity of the injection preserves the order.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition81
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem_toElementMap_inj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem

/-- **Proposition 8.2, second half.** `|D|` is order-isomorphic to the fixed-point set of
`a = retractionOfSubsystem h`, via `x ↦ i(x)` with inverse `y ↦ j(y)`. -/
def elementIso (h : D ◁ E) :
    D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y} where
  toFun x := ⟨h.inj.toElementMap x, retractionOfSubsystem_toElementMap_inj h x⟩
  invFun y := h.proj.toElementMap y.1
  left_inv x := by
    have h1 : h.proj.toElementMap (h.inj.toElementMap x) = (h.proj.comp h.inj).toElementMap x :=
      (toElementMap_comp h.proj h.inj x).symm
    show h.proj.toElementMap (h.inj.toElementMap x) = x
    rw [h1, h.proj_comp_inj, toElementMap_idMap]
  right_inv y := by
    apply Subtype.ext
    have hfix : (h.inj.comp h.proj).toElementMap y.1 = y.1 := y.2
    have h1 : (h.inj.comp h.proj).toElementMap y.1 = h.inj.toElementMap (h.proj.toElementMap y.1) :=
      toElementMap_comp h.inj h.proj y.1
    show h.inj.toElementMap (h.proj.toElementMap y.1) = y.1
    rw [← h1]; exact hfix
  map_rel_iff' := by
    intro x x'
    show h.inj.toElementMap x ≤ h.inj.toElementMap x' ↔ x ≤ x'
    constructor
    · intro hle
      have hmono := h.proj.toElementMap_mono hle
      have h1 : h.proj.toElementMap (h.inj.toElementMap x) = (h.proj.comp h.inj).toElementMap x :=
        (toElementMap_comp h.proj h.inj x).symm
      have h2 : h.proj.toElementMap (h.inj.toElementMap x') = (h.proj.comp h.inj).toElementMap x' :=
        (toElementMap_comp h.proj h.inj x').symm
      rw [h1, h2, h.proj_comp_inj, toElementMap_idMap, toElementMap_idMap] at hmono
      exact hmono
    · intro hle
      exact h.inj.toElementMap_mono hle

end Subsystem

end DomainTheory.NeighbourhoodSystems
