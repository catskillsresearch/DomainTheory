/-ai
A function token belonging to a finset that is consistent at stage n+1 has both component finsets consistent at stage n.

An auxiliary induction produces an earlier stage at which both components are consistent. Stage zero is impossible, because it has no function tokens. The left successor alternative lifts that earlier witness, and the right successor alternative uses the well-formedness clause at the preceding stage. Monotonicity then raises the earlier stage to n.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_mono

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)





















theorem LamConN_fun_wf {n : ℕ} {u : Finset (RawLamToken α)}
    {p : List (RawLamToken α) × List (RawLamToken α)}
    (hu : LamConN A (n + 1) u) (hp : p ∈ lamFunFinset u) :
    LamConN A n (listToFinset p.1) ∧ LamConN A n (listToFinset p.2) := by
  have aux {m : ℕ} {w : Finset (RawLamToken α)}
      (hw : LamConN A m w) (hq : p ∈ lamFunFinset w) :
      ∃ k, k + 1 ≤ m ∧
        LamConN A k (listToFinset p.1) ∧ LamConN A k (listToFinset p.2) := by
    induction m generalizing w with
    | zero =>
      exact False.elim (by
        have : p ∈ (∅ : Finset _) := by rw [← hw.2]; exact hq
        exact Finset.notMem_empty p this)
    | succ m ih =>
      rcases hw with hw | ⟨_, hWF, _⟩
      · rcases ih hw hq with ⟨k, hk, hk'⟩
        exact ⟨k, Nat.le_succ_of_le hk, hk'⟩
      · exact ⟨m, Nat.le_refl _, hWF p hq⟩
  rcases aux hu hp with ⟨k, hk, h1, h2⟩
  have hk' : k ≤ n := Nat.le_of_succ_le_succ hk
  exact ⟨LamConN_mono A hk' h1, LamConN_mono A hk' h2⟩

end InfoSys
end DomainTheory.InformationSystems
