/-ai
If A embeds in B, then the function space from A into C embeds in the function space from B into C.

Turn the embedding into a projection pair by composing its isomorphism part with its subsystem part. Placing the projection and the injection of that pair in the contravariant argument of the function-space combinator, with the identity on C in the covariant argument, yields a projection pair of function spaces. The projection-after-injection composite is the identity by the composition law for the combinator, the projection-pair law, and the combinator on identities. The other composite lies below the identity by the composition law, monotonicity in the contravariant argument, cancellation of the identity, and the combinator on identities. A projection pair determines an embedding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.expMap_mono_left

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


section General

variable {α β γ δ : Type*}

/-- **Contravariant functoriality of `⊴` in the function-space's domain argument.** `A ⊴ B ⟹
(A → C) ⊴ (B → C)` for any `C`: precompose/postcompose with the given projection pair via
`expMap`. -/
theorem funSpace_dom_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : funSpace A C ⊴ funSpace B C := by
  obtain ⟨D', hD'B, ⟨eAD'⟩⟩ := h
  set p : ProjPair A B := (ProjPair.ofIso eAD').comp (ProjPair.ofSubsystem hD'B) with hp
  refine trianglelefteq_of_projectionPair (expMap p.proj (idMap C)) (expMap p.inj (idMap C))
    ?_ ?_
  · have hcomp := (expMap_comp p.proj (idMap C) p.inj (idMap C)).symm
    rw [hcomp, p.proj_comp_inj, idMap_comp]
    exact expMap_id
  · calc (expMap p.proj (idMap C)).comp (expMap p.inj (idMap C))
        = expMap (p.inj.comp p.proj) ((idMap C).comp (idMap C)) :=
          (expMap_comp p.inj (idMap C) p.proj (idMap C)).symm
      _ ≤ expMap (idMap B) ((idMap C).comp (idMap C)) :=
          expMap_mono_left p.inj_comp_proj_le _
      _ = expMap (idMap B) (idMap C) := by rw [idMap_comp]
      _ = idMap (funSpace B C) := expMap_id

end General
end DomainTheory.NeighbourhoodSystems
