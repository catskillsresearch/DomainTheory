/-ai
If A is a retract of B, then the product of any neighbourhood system C with A is a retract of the product of C with B.

Commute the product so that the varying factor stands on the left, apply the left-hand functoriality of the retract relation, and commute back. The three retracts compose.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.prod_left_trianglelefteq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


section General

variable {α β γ δ : Type*}

/-- **Covariant functoriality of `⊴` in `prod`'s right argument.** `A ⊴ B ⟹ prod C A ⊴ prod C B`,
obtained from `prod_left_trianglelefteq` by conjugating with `prod`'s commutativity
(`Exercise315.prod_comm_isomorphic`). -/
theorem prod_right_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : prod C A ⊴ prod C B := by
  have h1 : prod C A ⊴ prod A C :=
    (prod_comm_isomorphic (V₀ := C) (V₁ := A)).elim fun e => ⟨_, Subsystem.refl _, ⟨e⟩⟩
  have h2 : prod A C ⊴ prod B C := prod_left_trianglelefteq C h
  have h3 : prod B C ⊴ prod C B :=
    (prod_comm_isomorphic (V₀ := B) (V₁ := C)).elim fun e => ⟨_, Subsystem.refl _, ⟨e⟩⟩
  exact trianglelefteq_trans (trianglelefteq_trans h1 h2) h3

end General
end DomainTheory.NeighbourhoodSystems
