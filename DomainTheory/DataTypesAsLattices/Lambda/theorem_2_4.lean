module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















/-- **Scott 1976, Theorem 2.4 (The combinator theorem).** -/
theorem theorem_2_4 : IsCombinatory zeroC ∧ IsCombinatory sucC ∧ IsCombinatory predC ∧
    IsCombinatory condC ∧ IsCombinatory Kcomb ∧ IsCombinatory Scomb :=
  ⟨.zero, .suc, .pred, .cond, .K, .S⟩

end DomainTheory.DataTypesAsLattices
