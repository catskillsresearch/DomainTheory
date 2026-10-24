module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Trianglelefteq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.IsGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Dprime
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.toEl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.ofEl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.dprimeEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_exists
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_mono'
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_fst_unique
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_snd_unique
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.mem_Dprime
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Dprime_subsystem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)


/-- **Lemma 6.15 (Scott 1981, PRG-19).** A projection pair `i : D → E`, `j : E → D` with
`j ∘ i = I_D` and `i ∘ j ⊆ I_E` exhibits `D` as a subdomain of `E`: `D ⊴ E`. This is the converse
of Proposition 6.12 (`Subsystem.projectionPair`). -/
theorem trianglelefteq_of_projectionPair (hji : j.comp i = idMap D)
    (hij : i.comp j ≤ idMap E) : D ⊴ E :=
  ⟨Dprime i j, Dprime_subsystem i j, ⟨dprimeEquiv i j hji hij⟩⟩

end ProjectionPair
end DomainTheory.NeighbourhoodSystems
