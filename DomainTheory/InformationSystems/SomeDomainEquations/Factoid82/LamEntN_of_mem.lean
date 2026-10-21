/-ai
A finite set of raw lambda tokens that is consistent at stage n entails, at that same stage, every raw token it contains. This is Scott's membership entailment, the reflexivity of entailment on raw tokens.

The proof inducts on the stage. At stage zero, bottom is the consistency; an atom is consistent, its atom set is nonempty by membership, and the underlying information system entails it by reflexivity; a function token would lie in the empty function set. At a successor stage, consistency at the previous stage gives the previous-stage entailment by the inductive hypothesis, placed in the left disjunct. Under the new consistency clause, bottom is that clause, and an atom would lie in the empty atom set. A function token is witnessed by the singleton of its own pair. Membership of the witness is the pair itself, and the input and output entailments at the previous stage are the inductive hypothesis applied to the well-formedness of that pair, after the output union of the singleton is rewritten as the output list.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_fun_wf

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


/-- Membership entailment at a fixed stage (Scott (v) / ent_refl on raw tokens). -/
theorem LamEntN_of_mem {n : ℕ} {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (hu : LamConN A n u) (ht : t ∈ u) : LamEntN A n u t := by
  induction n generalizing u t with
  | zero =>
    match t with
    | .bot => exact hu
    | .atom x =>
      exact ⟨hu, Finset.ne_empty_of_mem (mem_lamAtomFinset.2 ht),
        A.ent_refl hu.1 (mem_lamAtomFinset.2 ht)⟩
    | .funTok _ _ =>
      exact False.elim (by
        have hp : (_, _) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        rw [hu.2] at hp; exact Finset.notMem_empty _ hp)
  | succ n ih =>
    rcases hu with hu | hRight
    · exact Or.inl (ih hu ht)
    · have huFull : LamConN A (n + 1) u := Or.inr hRight
      match t with
      | .bot => exact Or.inr huFull
      | .atom x =>
        exact False.elim (by
          have : x ∈ lamAtomFinset u := mem_lamAtomFinset.2 ht
          rw [hRight.1] at this; exact Finset.notMem_empty x this)
      | .funTok xs ys =>
        have hmem : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        have hWF := LamConN_fun_wf A huFull hmem
        refine Or.inr ⟨huFull, hRight.1, hWF.1, hWF.2, ⟨{(xs, ys)}, ?_, ?_, ?_⟩⟩
        · intro p hp
          have : p = (xs, ys) := Finset.mem_singleton.mp hp
          subst this
          exact hmem
        · intro p hp t ht'
          have : p = (xs, ys) := Finset.mem_singleton.mp hp
          subst this
          exact ih hWF.1 ht'
        · intro t ht'
          rw [lamOutputUnion_singleton (xs, ys)]
          exact ih hWF.2 ht'

end InfoSys
end DomainTheory.InformationSystems
