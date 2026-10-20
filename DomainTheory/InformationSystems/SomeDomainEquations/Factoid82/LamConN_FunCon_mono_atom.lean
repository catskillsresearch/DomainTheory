module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_down_atom

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)





















/-- Apply a stage-`k` FunCon at stage `m ≥ k` when the input union has no function tokens. -/
theorem LamConN_FunCon_mono_atom {k m : ℕ} (hkm : k ≤ m)
    {u : Finset (RawLamToken α)}
    (hFun : ∀ s ⊆ lamFunFinset u,
      LamConN A k (lamInputUnion s) → LamConN A k (lamOutputUnion s))
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u)
    (hIn : LamConN A m (lamInputUnion s))
    (hF : lamFunFinset (lamInputUnion s) = ∅) :
    LamConN A m (lamOutputUnion s) := by
  have h0 := LamConN_down_atom A hIn hF
  have hk : LamConN A k (lamInputUnion s) := LamConN_mono A (Nat.zero_le k) h0
  exact LamConN_mono A hkm (hFun s hs hk)

end InfoSys
end DomainTheory.InformationSystems
