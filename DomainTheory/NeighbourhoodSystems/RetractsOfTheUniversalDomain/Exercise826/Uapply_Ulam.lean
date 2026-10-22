module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- **Faithfulness (`β`-soundness) of the self-hosted encoding.** Applying the self-hosted
abstraction of `f` recovers `f` itself: `Uapply (Ulam f) x = f(x)`. The internal `λ`-calculus of
`𝒰` literally computes the same thing as the "outside" one it is modelling — this is the actual
content of "the pay-off," beyond bare notation. Uses only `jArrow_comp_iArrow : j_→∘i_→ = I` (the
retraction half of Definition 8.9's fixed pair) and `evalMap`'s defining equation
(`evalMap_apply`). -/
theorem Uapply_Ulam (f : ApproximableMap U U) (x : U.Element) :
    Uapply (Ulam f) x = f.toElementMap x := by
  have hround : toApproxMap (toFilter f) = f := by
    have he := (funSpaceEquiv U U).apply_symm_apply f
    rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
  unfold Uapply Ulam
  have h1 : jArrow.toElementMap (iArrow.toElementMap (toFilter f))
      = (jArrow.comp iArrow).toElementMap (toFilter f) :=
    (toElementMap_comp jArrow iArrow (toFilter f)).symm
  rw [h1, jArrow_comp_iArrow, toElementMap_idMap, evalMap_apply, hround]

end DomainTheory.NeighbourhoodSystems
