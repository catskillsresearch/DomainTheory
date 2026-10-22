module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.iter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.isoOfEq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colimIso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.iSupRho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.subsystem_cast
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rec_trans
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_cast
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.set_rec_trans
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dceq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dchain
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.chain_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys_sub_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colimCeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys_sub_Tcolim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_sub_Tcolim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim_sub_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim_eq_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.domainObj_ext
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colimObj_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho_mono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}


/-- The colimit `𝒟` as a `T`-algebra, with structure map the iso `T(𝒟) → 𝒟`. -/
abbrev colimAlg (s : Setup.{w}) : TAlgebra s.T :=
  ⟨⟨s.Tok, colim s⟩, (colimIso s).hom⟩


/-- The colimit `𝒟` as a category object `⟨Tok, 𝒟⟩`. -/
abbrev objColim (s : Setup.{w}) : DomainObj := ⟨s.Tok, colim s⟩

/-- The `n`-th tower system `Tⁿ({Γ})` as a category object `⟨Tok, Tⁿ({Γ})⟩`. -/
abbrev objDsys (s : Setup.{w}) (n : ℕ) : DomainObj := ⟨s.Tok, Dsys s n⟩

/-- `T(ρₙ)` as an endomorphism of `T(𝒟)`, with the category objects pinned (they cannot be inferred
from `rho s n`'s `ApproximableMap` type alone). -/
abbrev Tmap_rho (s : Setup.{w}) (n : ℕ) :
    ApproximableMap (s.T.obj (objColim s)).sys (s.T.obj (objColim s)).sys :=
  s.T.map (X := objColim s) (Y := objColim s) (rho s n)

@[simp] theorem Dsys_zero (s : Setup.{w}) : Dsys s 0 = s.Γ := rfl

end Theorem614
end DomainTheory.NeighbourhoodSystems
