module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510





section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)



variable {P}















/-- **Exercise 7.15 (Scott 1981, PRG-19) — the infinite iterate `D^∞` is effectively given.** -/
theorem iterSys_isEffectivelyGiven (e : V.IsEffectivelyGiven) :
    (iterSys V).IsEffectivelyGiven := by
  obtain ⟨Q⟩ := e
  exact ⟨iterPresentation (P := Q)⟩

end Iterate
end DomainTheory.NeighbourhoodSystems
