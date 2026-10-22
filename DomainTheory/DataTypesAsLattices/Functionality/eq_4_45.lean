module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp_typed
public import DomainTheory.DataTypesAsLattices.Functionality.Htyped_typed
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun_decode
public import DomainTheory.DataTypesAsLattices.Functionality.Hcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.45).** Encoded terms live in `exp`, `ℋ⟦τ⟧` is typed
`env → lamb`, and the continuous `ℋ` decodes `encodeExp τ` to `ℋ⟦τ⟧`. -/
theorem eq_4_45 (τ : LambTerm) :
    typed (encodeExp τ) expR ∧
      typed (Htyped τ) (arrowR envR lambR) ∧
        funOf Hcomb (encodeExp τ) = Htyped τ := by
  refine ⟨encodeExp_typed τ, Htyped_typed τ, ?_⟩
  rw [Hcomb_app, ← encodeExp_typed τ, Hfun_decode]
  rfl

end DomainTheory.DataTypesAsLattices
