/-ai
Every abstract-syntax encoding of a lambda term is typed by the expression retract.

Induction on the term. A variable rewrites the encoding and equation (4.44), then uses the zeroth left injection of the seven-fold sum on the integer typing of the numeral. Zero uses the first injection on the typing of bottom. Successor and predecessor use the second and third injections with the inductive hypothesis. A conditional uses the fourth injection after rewriting typedness through the four-fold tensor and the four projections of the four-sequence back to the four inductive hypotheses. An application uses the fifth injection and the typing of a pair sequence by a tensor of expression retracts. An abstraction uses the sixth injection and the typing of a pair sequence by the tensor of the integer retract with the expression retract.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.typed_pairSeq_tensorR
public import DomainTheory.DataTypesAsLattices.Functionality.tensor4_app
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_two
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_three
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
    rw [typed, tensor4_app, seq4_app_zero, seq4_app_one, seq4_app_two,
      seq4_app_three, ← ihθ, ← ihτ, ← ihσ, ← ihρ]
  | app τ σ ihτ ihσ =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl5 ?_
    exact (typed_pairSeq_tensorR expR expR _ _).mpr ⟨ihτ, ihσ⟩
  | lam n τ ih =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl6 ?_
    exact (typed_pairSeq_tensorR intR expR _ _).mpr ⟨typed_ofNat_intR n, ih⟩

end DomainTheory.DataTypesAsLattices
