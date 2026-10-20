module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)



























theorem LamConN_insert_bot {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) : LamConN A n (insert (.bot : RawLamToken α) u) := by
  induction n generalizing u with
  | zero =>
    exact ⟨by rw [lamAtomFinset_insert_bot]; exact hu.1,
      by rw [lamFunFinset_insert_bot]; exact hu.2⟩
  | succ n ih =>
    rcases hu with hu | ⟨hA, hWF, hFun⟩
    · exact Or.inl (ih hu)
    · exact Or.inr ⟨by rw [lamAtomFinset_insert_bot]; exact hA,
        fun p hp => hWF p (by rwa [lamFunFinset_insert_bot] at hp),
        fun s hs hIn =>
          hFun s (fun p hp => by rw [← lamFunFinset_insert_bot u]; exact hs hp) hIn⟩

end InfoSys
end DomainTheory.InformationSystems
