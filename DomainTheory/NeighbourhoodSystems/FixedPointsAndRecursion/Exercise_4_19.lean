module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.seqPeano

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap BitDom SeqDom DomainTheory.NeighbourhoodSystems.SeqPeano

theorem example_419 :
    (∀ (b : Bool) (σ : Str), ([] : Str) ≠ b :: σ) ∧
    (∀ (σ : Str), oneMap.toElementMap (strBot σ) = oneDef (strBot σ)) ∧
    (∀ (σ : Str), oneMap.toElementMap (strElem σ) = oneDef (strElem σ)) ∧
    (∀ (σ τ : Str), (false :: σ) ≠ (true :: τ)) ∧
    (∀ {b : Bool} {σ τ : Str}, b :: σ = b :: τ → σ = τ) ∧
    (∀ (P : Str → Prop), P [] → (∀ b σ, P σ → P (b :: σ)) → ∀ σ, P σ) :=
  ⟨peano_nil_ne_cons, one_def_strBot, one_def_strElem,
    peano_cons_disjoint, @peano_cons_injective, peano_induction⟩

