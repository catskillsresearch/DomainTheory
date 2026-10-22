
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app3
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app2_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 7.3 (iii).**
`S : (A → (B → C)) → ((A → B) → (A → C))`. -/
theorem theorem_7_3_iii (A B C : RestrictedEquiv) :
    (arrowE (arrowE A (arrowE B C))
      (arrowE (arrowE A B) (arrowE A C))).mem Scomb := by
  refine ⟨Scomb_isGraph, Scomb_isGraph, ?_⟩
  intro f f' hf
  refine ⟨Scomb_app_isGraph f, Scomb_app_isGraph f', ?_⟩
  intro g g' hg
  refine ⟨Scomb_app2_isGraph f g, Scomb_app2_isGraph f' g', ?_⟩
  intro x x' hx
  have hgx : (arrowE A B).rel g g' := hg
  have hfx : (arrowE A (arrowE B C)).rel f f' := hf
  have hB : B.rel (funOf g x) (funOf g' x') := hgx.2.2 x x' hx
  have hBC : (arrowE B C).rel (funOf f x) (funOf f' x') := hfx.2.2 x x' hx
  simpa [Scomb_app3] using hBC.2.2 (funOf g x) (funOf g' x') hB

end DomainTheory.DataTypesAsLattices
