/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
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
