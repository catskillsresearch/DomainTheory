module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.tagInj
public import DomainTheory.DataTypesAsLattices.Retracts.seq4
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Enumeration.Zcomb
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Retracts.typed_more
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.eq_4_44
public import DomainTheory.DataTypesAsLattices.Retracts.expR
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.plus7
public import DomainTheory.DataTypesAsLattices.Retracts.tensor4
public import DomainTheory.DataTypesAsLattices.Retracts.typed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def encodeExp : LambTerm → Pomega
  | .var n => tagInj 0 (ofNat n)
  | .zero => tagInj 1 botElem
  | .succ τ => tagInj 2 (encodeExp τ)
  | .pred τ => tagInj 3 (encodeExp τ)
  | .condq θ τ σ ρ =>
      tagInj 4 (seq4 (encodeExp θ) (encodeExp τ) (encodeExp σ) (encodeExp ρ))
  | .app τ σ => tagInj 5 (pairSeq (encodeExp τ) (encodeExp σ))
  | .lam n τ => tagInj 6 (pairSeq (ofNat n) (encodeExp τ))

namespace encodeExp

theorem typed : ∀ τ : LambTerm, typed (encodeExp τ) expR := by
  intro τ
  induction τ with
  | var n =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    exact plus7.typed_inl0 (typed.ofNat_intR n)
  | zero =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    exact plus7.typed_inl1 typed.bot_botElem
  | succ τ ih =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    exact plus7.typed_inl2 ih
  | pred τ ih =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    exact plus7.typed_inl3 ih
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    refine plus7.typed_inl4 ?_
    rw [DomainTheory.DataTypesAsLattices.typed, tensor4.app, seq4.zero, seq4.one, seq4.two,
      seq4.three, ← ihθ, ← ihτ, ← ihσ, ← ihρ]
  | app τ σ ihτ ihσ =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    refine plus7.typed_inl5 ?_
    exact (typed.pairSeq_tensorR expR expR _ _).mpr ⟨ihτ, ihσ⟩
  | lam n τ ih =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    refine plus7.typed_inl6 ?_
    exact (typed.pairSeq_tensorR intR expR _ _).mpr ⟨typed.ofNat_intR n, ih⟩

end encodeExp

def expTag (e : Pomega) : Pomega := funOf e (ofNat 0)

def expPayload (e : Pomega) : Pomega := funOf e (ofNat 1)

def eraseTag (j : ℕ) (u : Pomega) : Pomega :=
  {p | p ∈ u ∧ ∀ k, p ≠ pair j k}

namespace eraseTag
theorem Z_finite (p q m : ℕ) :
    eraseTag (max p q + 1) (Z m (e p) (e q)) = Z m (e p) (e q) := by
  ext k
  constructor
  · exact fun hk => hk.1
  · intro hk
    exact ⟨hk, fun r hkr => Z.finite_no_tag p q m r (hkr ▸ hk)⟩

theorem Z_finite_union (p q m : ℕ) :
    eraseTag (max p q + 1)
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z m (e p) (e q) := by
  ext k
  constructor
  · intro ⟨hk, hnot⟩
    rcases hk with hk | hk
    · exact hk
    · exact (hnot m (by simpa using hk)).elim
  · intro hk
    exact ⟨Or.inl hk, fun r hkr => Z.finite_no_tag p q m r (hkr ▸ hk)⟩

end eraseTag


end DomainTheory.DataTypesAsLattices
