module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_fun_wf

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

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
