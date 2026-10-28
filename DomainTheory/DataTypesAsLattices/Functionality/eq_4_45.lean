module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import DomainTheory.DataTypesAsLattices.Retracts.envR
public import DomainTheory.DataTypesAsLattices.Retracts.expR
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.Htyped
public import DomainTheory.DataTypesAsLattices.Functionality.Hcomb
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp_typed
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_45 (τ : LambTerm) :
    typed (encodeExp τ) expR ∧
      typed (Htyped τ) (arrowR envR lambR) ∧
        funOf Hcomb (encodeExp τ) = Htyped τ := by
  refine ⟨encodeExp_typed τ, Htyped.typed τ, ?_⟩
  rw [Hcomb.app, ← encodeExp_typed τ, Hfun.decode]
  rfl

end DomainTheory.DataTypesAsLattices
