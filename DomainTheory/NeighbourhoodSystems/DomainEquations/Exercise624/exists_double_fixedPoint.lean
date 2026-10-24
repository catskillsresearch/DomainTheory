module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.fTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Dsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Esol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Fsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Gsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.fTok_GammaD_GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok_GammaD_GammaE

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624


/-- **The double fixed point (token level).** There is a pair of token sets `(Γ_D, Γ_E)`, both
containing `Λ`, that solve the two coupled token equations `tok(D + (D×E)) = Γ_D` and
`tok(D + E) = Γ_E` simultaneously. -/
theorem exists_double_fixedPoint :
    ∃ Γd Γe : Set Str, ([] : Str) ∈ Γd ∧ ([] : Str) ∈ Γe ∧
      fTok Γd Γe = Γd ∧ gTok Γd Γe = Γe :=
  ⟨GammaD, GammaE, nil_mem_GammaD, nil_mem_GammaE, fTok_GammaD_GammaE, gTok_GammaD_GammaE⟩

end Exercise624
end DomainTheory.NeighbourhoodSystems
