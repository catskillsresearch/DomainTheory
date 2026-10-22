module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_singleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.strElemN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_singleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

theorem consMapN_strElem (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strElemN σ) = strElemN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXsing⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc ({a :: σ} : Set (Strn A)) = prependN [a] {σ} := by rw [prependN_singleton]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXsing
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memCn_singleton σ, subset_rfl⟩, memCn_singleton σ, hY, ?_⟩
    rw [show prependN [a] ({σ} : Set (Strn A)) = {a :: σ} by rw [prependN_singleton]; rfl]
    exact hsub

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
