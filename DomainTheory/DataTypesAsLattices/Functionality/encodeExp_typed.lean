module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.expR
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.typed_pairSeq_tensorR
public import DomainTheory.DataTypesAsLattices.Functionality.tensor4_app
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_44
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl0
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl1
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl2
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl3
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl4
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl5
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl6
public import DomainTheory.DataTypesAsLattices.Functionality.typed_ofNat_intR
public import DomainTheory.DataTypesAsLattices.Functionality.typed_bot_botElem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem encodeExp_typed : ∀ τ : LambTerm, typed (encodeExp τ) expR := by
  intro τ
  induction τ with
  | var n =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl0 (typed_ofNat_intR n)
  | zero =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl1 typed_bot_botElem
  | succ τ ih =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl2 ih
  | pred τ ih =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl3 ih
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl4 ?_
    rw [typed, tensor4_app, seq4_app.zero, seq4_app.one, seq4_app.two,
      seq4_app.three, ← ihθ, ← ihτ, ← ihσ, ← ihρ]
  | app τ σ ihτ ihσ =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl5 ?_
    exact (typed_pairSeq_tensorR expR expR _ _).mpr ⟨ihτ, ihσ⟩
  | lam n τ ih =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl6 ?_
    exact (typed_pairSeq_tensorR intR expR _ _).mpr ⟨typed_ofNat_intR n, ih⟩

end DomainTheory.DataTypesAsLattices
