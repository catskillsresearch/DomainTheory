module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_insert_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_nonempty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_fun
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_atom

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Weaken Ent across inserting another token entailed by the same set. -/
theorem LamEntDepth_weaken_insert {u : Finset (RawLamToken α)}
    {a x : RawLamToken α}
    (hu' : LamConDepth A (insert a u))
    (hx : LamEntDepth A u x) (ha : LamEntDepth A u a) :
    LamEntDepth A (insert a u) x := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have huv : u ⊆ insert a u := Finset.subset_insert a u
  match x with
  | .bot => exact LamEntDepth.bot hu'
  | .atom z =>
    cases decidableEq_finset (lamFunFinset (insert a u)) ∅ with
    | isTrue hF =>
      exact LamEntDepth_weaken_atom A huv hu' hF hx
    | isFalse hF =>
      have hAt := ((LamConDepth_of_fun_nonempty A hF).1 hu').1
      cases hx with
      | atom _ _ hne _ =>
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
        exact False.elim (Finset.notMem_empty y (by
          have := lamAtomFinset_mono huv hy; rwa [hAt] at this))
  | .funTok xs ys =>
    cases decidableEq_finset (lamFunFinset (insert a u)) ∅ with
    | isFalse hF =>
      have hAv := ((LamConDepth_of_fun_nonempty A hF).1 hu').1
      exact LamEntDepth_weaken_fun A huv hu' hAv hx
    | isTrue hF =>
      cases ha with
      | bot _ =>
        cases hx with
        | funTok hu hA hConIn hConOut hs hWorld hInCompat hEntIn hEntOut =>
          have hAv : lamAtomFinset (insert (.bot : RawLamToken α) u) = ∅ := by
            rw [lamAtomFinset_insert_bot]; exact hA
          exact LamEntDepth.funTok hu' hAv hConIn hConOut
            (by rw [lamFunFinset_insert_bot]; exact hs)
            (by rw [lamFunFinset_insert_bot]; exact hWorld)
            hInCompat hEntIn hEntOut
      | atom _ _ hne _ =>
        cases hx with
        | funTok _ hA _ _ _ _ _ _ _ =>
          obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
          exact False.elim (Finset.notMem_empty y (by rwa [hA] at hy))
      | funTok _ _ _ _ _ _ _ _ _ =>
        -- `a` refined to funTok, so fun (insert a u) ≠ ∅, contradicting hF
        simp only [lamFunFinset_insert_funTok] at hF
        exact False.elim (Finset.notMem_empty _ (hF ▸ Finset.mem_insert_self _ _))

end InfoSys

end DomainTheory.InformationSystems
