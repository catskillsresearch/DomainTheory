/-ai
For every homomorphism g, the composite of g with the zero projection equals the zero Kleene iterate, the constant bottom map. The identity does not depend on which homomorphism is chosen.

Extensionality and the relational form of composition reduce the claim to pairs. A factorisation through the zero projection has middle neighbourhood equal to the master of Exp, and strictness of g sends it to the master of the carrier, which is the constant-bottom relation. Conversely, a constant-bottom pair is witnessed by the master of Exp, which the zero projection relates to the source, together with the master relation of g.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ext
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Exp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ExpAlg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho_zero_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.TexpF

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

/-- The base of the recursion: `g ∘ ρ₀ = ⊥ = val₀`, independent of `g`. -/
theorem gcomp_rho_zero (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1.comp (rho hN 0) = descRel hN B 0 := by
  apply ApproximableMap.ext
  intro A Z
  rw [comp_rel]
  constructor
  · rintro ⟨E, hrho, hg⟩
    rw [rho_zero_rel] at hrho
    obtain ⟨hcA, rfl⟩ := hrho
    have hZ : Z = B.carrier.sys.master := g.hom.2 hg
    exact ⟨hcA, by rw [NeighborhoodSystem.mem_bot]; exact hZ⟩
  · rintro ⟨hcA, hZ⟩
    rw [NeighborhoodSystem.mem_bot] at hZ
    subst hZ
    exact ⟨(Exp N hN).sys.master, (rho_zero_rel hN).mpr ⟨hcA, rfl⟩, g.hom.1.master_rel⟩

end Uniqueness

end Exercise619

end DomainTheory.NeighbourhoodSystems
