module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seq2_tag_ne (x y : Pomega) :
    seq2 (ofNat 0) x ≠ seq2 (ofNat 1) y := by
  intro h
  have hfun := congrArg (fun w => funOf w (ofNat 0)) h
  have hx : (0 : ℕ) ∈ funOf (seq2 (ofNat 0) x) (ofNat 0) :=
    ⟨1, fun k hk =>
      match k, hk with
      | 0, _ => rfl
      | k + 1, hk =>
        False.elim (Bool.false_ne_true
          (((Nat.testBit_succ 1 k).trans (Nat.zero_testBit k)).symm.trans hk)),
      ⟨1, 0, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hy : (0 : ℕ) ∉ funOf (seq2 (ofNat 1) y) (ofNat 0) := by
    intro ⟨k, hk, hp⟩
    rcases hp with ⟨k', m, heq, hm⟩
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    rcases hm with ⟨h1, _⟩ | ⟨_, ⟨t, ht⟩⟩
    · exact Nat.zero_ne_one h1
    · exact Nat.succ_ne_zero t (hk ht)
  exact hy (hfun ▸ hx)

end DomainTheory.DataTypesAsLattices
