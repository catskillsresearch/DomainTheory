module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

@[simp] theorem papplyEval_rel {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {Φ : Set (Set (ApproximableMap V W))} {A : Set (Set α)} {B : Set (Set β)} :
    (papplyEval V W).rel Φ A B ↔ (funSpace V W).PDmem Φ ∧ V.PDmem A ∧ W.PDmem B ∧
      ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, (eval V W).rel G X Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
