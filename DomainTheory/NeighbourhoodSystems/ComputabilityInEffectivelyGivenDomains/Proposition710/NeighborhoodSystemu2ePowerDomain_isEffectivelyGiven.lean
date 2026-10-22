/-ai
Proposition 7.10. The Smyth power domain of an effectively given neighbourhood system is effectively given. The consistency decider is taken from the given presentation inside the existence proof.

From an effective presentation, take its consistency decider. The power-domain presentation built from that decider is a computable presentation, because the decider's specification on a paired index, rewritten by the unpairing equations, is the required consistency test.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive


/-- **Proposition 7.10 (Scott 1981, PRG-19).** The Smyth power domain `ℙ𝒟` is a neighbourhood system
(`PowerDomain`), and it is **effectively given** whenever `𝒟` is. The consistency decider is obtained
from `𝒟`'s presentation inside the `Nonempty` proof (extraction into a `Prop` needs no choice). -/
theorem NeighborhoodSystem.PowerDomain_isEffectivelyGiven {α : Type*} {V : NeighborhoodSystem α}
    (h : V.IsEffectivelyGiven) : V.PowerDomain.IsEffectivelyGiven := by
  obtain ⟨P⟩ := h
  obtain ⟨cons, hconsp, hconss⟩ := P.cons_computable
  refine ⟨V.PDPresentation P cons hconsp (fun a b => ?_)⟩
  have hb := hconss (Nat.pair a b)
  simp only [unpair_pair_fst, unpair_pair_snd] at hb
  exact hb.symm

end DomainTheory.NeighbourhoodSystems
