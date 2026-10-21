/-ai
If a finite set of raw lambda tokens is depth-consistent and contains a raw token, then the set depth-entails that token.

The proof strengthens the claim to the maximum of the finset depth of the set and the raw depth of the token, and uses strong induction on that bound. The bottom token is the bottom clause. An atom is handled by whether the function set of the set is empty. In the empty case the atom lies in a nonempty atom set, and the atom-world form of depth consistency gives reflexivity of entailment in the underlying information system. In the nonempty case that form makes the atom set empty, so the atom cannot belong to it. A function token is impossible when the function set is empty. When the function set is nonempty, depth consistency gives an empty atom set and consistency of both argument lists, and the token's pair belongs to the function set. The function-token clause uses the singleton witness of that pair. The input union of the singleton is the finite set of the input list, so emptiness of the function set of the input list passes to that union. Each input token has a strictly smaller induction bound, because its raw depth lies below the finset depth of the set and the finset depth of the input list lies below the raw depth of the function token, and the inductive hypothesis applies to the input list. Each output token is treated the same way after the output union of the singleton is rewritten as the finite set of the output list, using the corresponding strict bounds on the output side.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamAtomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_nonempty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_bot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem LamEntDepth_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (hu : LamConDepth A u) (ht : t ∈ u) : LamEntDepth A u t := by
  suffices ∀ M u t, Nat.max (finsetMaxDepth u) (rawDepth t) = M →
      LamConDepth A u → t ∈ u → LamEntDepth A u t from
    this _ _ _ rfl hu ht
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro u t hM hu ht
    match t with
    | .bot => exact LamEntDepth_bot A hu
    | .atom x =>
      cases decidableEq_finset (lamFunFinset u) ∅ with
      | isTrue hF =>
        have hx : x ∈ lamAtomFinset u := mem_lamAtomFinset.2 ht
        exact LamEntDepth.atom hu hF (Finset.ne_empty_of_mem hx)
          (A.ent_refl ((LamConDepth_of_fun_empty A hF).1 hu) hx)
      | isFalse hF =>
        have hA := ((LamConDepth_of_fun_nonempty A hF).1 hu).1
        have hx : x ∈ lamAtomFinset u := mem_lamAtomFinset.2 ht
        rw [hA] at hx; exact False.elim (Finset.notMem_empty x hx)
    | .funTok xs ys =>
      cases decidableEq_finset (lamFunFinset u) ∅ with
      | isTrue hF =>
        have : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        rw [hF] at this; exact False.elim (Finset.notMem_empty _ this)
      | isFalse hF =>
        have hu' := (LamConDepth_of_fun_nonempty A hF).1 hu
        rcases hu' with ⟨hA, hWF, _hFun⟩
        have hmem : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        have ⟨hConIn, hConOut⟩ := hWF (xs, ys) hmem
        refine LamEntDepth.funTok (s := {(xs, ys)}) hu hA hConIn hConOut
          (fun p hp => by
            have hp' : p = (xs, ys) := Finset.mem_singleton.mp hp
            exact hp' ▸ hmem) hF ?_ ?_ ?_
        · intro hxsF
          have hIn : lamInputUnion {(xs, ys)} = listToFinset xs := by
            rw [lamInputUnion_singleton]
          rw [hIn, hxsF]
        · intro p hp z hz
          have hp' : p = (xs, ys) := Finset.mem_singleton.mp hp
          subst hp'
          refine ih (Nat.max (finsetMaxDepth (listToFinset xs)) (rawDepth z))
            ?_ (listToFinset xs) z rfl hConIn hz
          have htok : .funTok xs ys ∈ u := mem_lamFunFinset.1 hmem
          have ht_lt : rawDepth z < finsetMaxDepth u :=
            Nat.lt_of_lt_of_le (rawDepth_funTok_gt_left ((mem_listToFinset).1 hz))
              (le_finsetMaxDepth_of_mem htok)
          have hxs_lt : finsetMaxDepth (listToFinset xs) < rawDepth (.funTok xs ys) :=
            finsetMaxDepth_list_lt_funTok xs ys
          rw [← hM]
          refine Nat.max_lt.2 ⟨
            Nat.lt_of_lt_of_le hxs_lt (Nat.le_max_right _ _),
            Nat.lt_of_lt_of_le ht_lt (Nat.le_max_left _ _)⟩
        · intro z hz
          rw [lamOutputUnion_singleton]
          refine ih (Nat.max (finsetMaxDepth (listToFinset ys)) (rawDepth z))
            ?_ (listToFinset ys) z rfl hConOut hz
          have ht_lt : rawDepth z < rawDepth (.funTok xs ys) :=
            rawDepth_funTok_gt_right ((mem_listToFinset).1 hz)
          have hys_lt : finsetMaxDepth (listToFinset ys) < rawDepth (.funTok xs ys) :=
            finsetMaxDepth_list_lt_funTok_out xs ys
          rw [← hM]
          refine Nat.max_lt.2 ⟨
            Nat.lt_of_lt_of_le hys_lt (Nat.le_max_right _ _),
            Nat.lt_of_lt_of_le ht_lt (Nat.le_max_right _ _)⟩

end InfoSys

end DomainTheory.InformationSystems
