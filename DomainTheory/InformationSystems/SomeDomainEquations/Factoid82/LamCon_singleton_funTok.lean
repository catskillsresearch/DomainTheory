/-ai
The singleton of a function token is consistent whenever both component finsets are consistent.

Take stages witnessing the two components and let k be their maximum. At stage k+1 the right-hand clause applies: there are no atoms, the only function token has components lifted to stage k by monotonicity, and a subcollection either equals that singleton, whose output union is the output component, or is empty, which is consistent at stage k.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_empty

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem LamCon_singleton_funTok (u v : List (RawLamToken α))
    (hu : LamCon A (listToFinset u)) (hv : LamCon A (listToFinset v)) :
    LamCon A ({.funTok u v} : Finset (RawLamToken α)) := by
  rcases hu with ⟨n, hu⟩
  rcases hv with ⟨m, hv⟩
  let k := max n m
  refine ⟨k + 1, Or.inr ⟨?_, ?_, ?_⟩⟩
  · exact lamAtomFinset_singleton_funTok u v
  · intro p hp
    have : p = (u, v) := by
      have h := Finset.mem_singleton.mp (by
        rw [← lamFunFinset_singleton_funTok u v]; exact hp)
      exact h
    subst this
    exact ⟨LamConN_mono A (Nat.le_max_left n m) hu,
      LamConN_mono A (Nat.le_max_right n m) hv⟩
  · intro s hs hIn
    have hFun : lamFunFinset ({.funTok u v} : Finset (RawLamToken α)) = {(u, v)} :=
      lamFunFinset_singleton_funTok u v
    rw [hFun] at hs
    if hmem : (u, v) ∈ s then
      have hsin : s = {(u, v)} := by
        ext p
        constructor
        · intro hp
          exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp (hs hp))
        · intro hp
          have : p = (u, v) := Finset.mem_singleton.mp hp
          subst this; exact hmem
      subst hsin
      rw [lamOutputUnion_singleton]
      exact LamConN_mono A (Nat.le_max_right n m) hv
    else
      have hempty : s = ∅ := by
        ext p
        constructor
        · intro hp
          exact False.elim (hmem (by
            have : p = (u, v) := Finset.mem_singleton.mp (hs hp)
            subst this; exact hp))
        · intro hp
          exact False.elim (Finset.notMem_empty p hp)
      subst hempty
      exact LamConN_empty A k

end InfoSys
end DomainTheory.InformationSystems
