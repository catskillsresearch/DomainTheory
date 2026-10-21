/-ai
An n-ary map is finitely Scott continuous when continuity is taken one argument at a time from the left. The zero-ary case holds outright. An (n + 1)-ary map is finitely Scott continuous when it is Scott continuous in the first argument for every choice of the remaining arguments, and each of those remaining maps is finitely Scott continuous.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Continuity of an n-ary map, taken one argument at a time from the left. -/
def IsScottContinuousFin : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Prop
  | 0, _ => True
  | n + 1, f =>
      (∀ xs : Fin n → Pomega, IsScottContinuous (fun x => f (Fin.cons x xs))) ∧
      (∀ x : Pomega, IsScottContinuousFin (fun xs : Fin n → Pomega => f (Fin.cons x xs)))

end DomainTheory.DataTypesAsLattices
