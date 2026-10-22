module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem envSet_comm {ρ : ℕ → Pomega} {i j : ℕ} (hij : i ≠ j) (v w : Pomega) :
    envSet (envSet ρ i v) j w = envSet (envSet ρ j w) i v := by
  funext k
  unfold envSet
  by_cases hj : k = j
  · subst hj
    simp [Function.update, hij.symm]
  · by_cases hi : k = i
    · subst hi
      simp [Function.update, hij]
    · simp [Function.update, hi, hj]

end DomainTheory.DataTypesAsLattices
