module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.myStep_subset

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}


/-- **Folding only ever shrinks the presented set.** -/
theorem myFoldl_subset
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) :
    ∀ (l : List ℕ) (r : ℕ), P.X (l.foldl (myStep P qChar cons) r) ⊆ P.X r := by
  intro l
  induction l with
  | nil => intro r; simp only [List.foldl_nil]; exact subset_rfl
  | cons e rest ih =>
    intro r
    rw [List.foldl_cons]
    exact (ih (myStep P qChar cons r e)).trans (myStep_subset hcons r e)

end DomainTheory.NeighbourhoodSystems
