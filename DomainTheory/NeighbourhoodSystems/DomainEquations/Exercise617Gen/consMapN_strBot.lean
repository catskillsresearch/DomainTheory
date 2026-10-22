module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.strBotN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

theorem consMapN_strBot (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strBotN σ) = strBotN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXcone⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc coneN (a :: σ) = prependN [a] (coneN σ) := by rw [prependN_coneN]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXcone
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, memCn_coneN σ, hY, ?_⟩
    rw [show prependN [a] (coneN σ) = coneN (a :: σ) by rw [prependN_coneN]; rfl]
    exact hsub

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
