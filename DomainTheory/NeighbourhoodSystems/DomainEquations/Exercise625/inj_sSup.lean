/-ai
The injection preserves least upper bounds of bounded sets: the image of the supremum equals the supremum of the image.

The image of the supremum lies below the supremum of the image because the Galois connection reduces that comparison to each member lying below the projection of the supremum of the image, and a second use of the Galois connection turns each image lying below that supremum into the required inequality. The supremum of the image lies below the image of the supremum because each image does, by monotonicity of the injection and the member lying below the supremum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.galois
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.inj_bounded

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair








/-- **Exercise 6.25 — `g` preserves `⊔` (not just *directed* unions).** For any bounded set `S`,
`g(⊔S) = ⊔ {g(s) ∣ s ∈ S}`. This is the characteristic property of a lower adjoint.

* `⊒`: `g(⊔S)` is an upper bound of `{g(s)}` since `s ⊑ ⊔S` and `g` is monotone.
* `⊑`: by the Galois connection it suffices that `⊔S ⊑ h(⊔{g(s)})`, i.e. that each `s ⊑ h(⊔{g(s)})`;
  by the Galois connection again this is `g(s) ⊑ ⊔{g(s)}`, true by `le_sSup`. -/
theorem inj_sSup (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    P.inj.toElementMap (D.sSup S hS) =
      E.sSup (P.inj.toElementMap '' S) (P.inj_bounded hS) := by
  apply le_antisymm
  · refine (P.galois _ _).mpr (D.sSup_le S hS fun s hs => ?_)
    refine (P.galois s _).mp ?_
    exact E.le_sSup _ (P.inj_bounded hS) ⟨s, hs, rfl⟩
  · refine E.sSup_le _ (P.inj_bounded hS) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact P.inj.toElementMap_mono (D.le_sSup S hS hs)

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
