/-ai
Inserting bottom preserves consistency at stage n.

Induct on the stage. At stage zero, the atom and function-token projections ignore bottom. At a successor stage, the left alternative uses the inductive hypothesis. The right alternative keeps an empty atom projection, leaves membership of function tokens unchanged, and transports the function clause along that equality.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

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
