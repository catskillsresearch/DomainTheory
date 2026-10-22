module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_exists_FunCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_FunCon_mono_atom

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


/-- Full FunCon at stage `n+1` (uses `exists_FunCon` + atom-input lift).
Nested function tokens in the input union remain for the general `ent_con` argument. -/
theorem LamConN_fun_FunCon_atom {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A (n + 1) u)
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hIn : LamConN A n (lamInputUnion s))
    (hF : lamFunFinset (lamInputUnion s) = ∅) :
    LamConN A n (lamOutputUnion s) := by
  if hempty : s = ∅ then
    subst hempty
    simpa [lamOutputUnion_empty] using LamConN_empty A n
  else
    have hne : lamFunFinset u ≠ ∅ := by
      obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hempty
      exact Finset.ne_empty_of_mem (hs hp)
    rcases LamConN_exists_FunCon A hu hne with ⟨k, hk, _, _, hFun⟩
    have hkn : k ≤ n := Nat.le_of_succ_le_succ hk
    exact LamConN_FunCon_mono_atom A hkn hFun hs hIn hF

end InfoSys
end DomainTheory.InformationSystems
